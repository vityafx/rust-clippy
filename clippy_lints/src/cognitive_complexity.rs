//! calculate cognitive complexity and warn about overly complex functions

use rustc::cfg::CFG;
use rustc::hir::intravisit::{walk_expr, NestedVisitorMap, Visitor};
use rustc::hir::*;
use rustc::lint::{LateContext, LateLintPass, LintArray, LintContext, LintPass};
use rustc::ty;
use rustc::{declare_tool_lint, impl_lint_pass};
use syntax::ast::Attribute;
use syntax::source_map::Span;

use crate::utils::{is_allowed, match_type, paths, span_help_and_lint, span_notes_and_lint, LimitStack};

declare_clippy_lint! {
    /// **What it does:** Checks for methods with high cognitive complexity.
    ///
    /// **Why is this bad?** Methods of high cognitive complexity tend to be hard to
    /// both read and maintain. Also LLVM will tend to optimize small methods better.
    ///
    /// **Known problems:** Sometimes it's hard to find a way to reduce the
    /// complexity.
    ///
    /// **Example:** No. You'll see it when you get the warning.
    pub COGNITIVE_COMPLEXITY,
    complexity,
    "functions that should be split up into multiple functions"
}

pub struct CognitiveComplexity {
    limit: LimitStack,
    verbosity: LimitStack,
}

impl CognitiveComplexity {
    pub fn new(limit: u64, verbosity: u64) -> Self {
        Self {
            limit: LimitStack::new(limit),
            verbosity: LimitStack::new(verbosity),
        }
    }
}

impl_lint_pass!(CognitiveComplexity => [COGNITIVE_COMPLEXITY]);

impl CognitiveComplexity {
    fn check<'a, 'tcx>(&mut self, cx: &'a LateContext<'a, 'tcx>, body: &'tcx Body, span: Span) {
        if span.from_expansion() {
            return;
        }

        let cfg = CFG::new(cx.tcx, body);
        let expr = &body.value;
        let n = cfg.graph.len_nodes() as u64;
        let e = cfg.graph.len_edges() as u64;
        if e + 2 < n {
            // the function has unreachable code, other lints should catch this
            return;
        }
        let cc = e + 2 - n;
        let mut helper = CCHelper {
            spans: Vec::new(),
            cx,
        };
        helper.visit_expr(expr);
        let match_arms = helper.spans.iter().filter(|(_, t)| *t == CCType::MatchArm).count() as u64;
        let divergence = helper.spans.iter().filter(|(_, t)| *t == CCType::Divergence).count() as u64;
        let short_circuits = helper.spans.iter().filter(|(_, t)| *t == CCType::ShortCircuit).count() as u64;
        let returns = helper.spans.iter().filter(|(_, t)| *t == CCType::Return).count() as u64;
        let ret_ty = cx.tables.node_type(expr.hir_id);
        let ret_adjust = if match_type(cx, ret_ty, &paths::RESULT) {
            returns
        } else {
            #[allow(clippy::integer_division)]
            (returns / 2)
        };


        if cc + divergence < match_arms + short_circuits {
            report_cc_bug(
                cx,
                cc,
                match_arms,
                divergence,
                short_circuits,
                // ret_adjust,
                returns,
                span,
                body.id().hir_id,
            );
        } else {
            let mut rust_cc = cc + divergence - match_arms - short_circuits;
            // let rust_cc = cc + divergence - match_arms - short_circuits;
            // prevent degenerate cases where unreachable code contains `return` statements
            if rust_cc >= ret_adjust {
                rust_cc -= ret_adjust;
            }
            if rust_cc > self.limit.limit() {
                // if rust_cc > self.verbosity.limit() {
                //     let mut notes: Vec<(Span, String)> = Vec::new();
                //     let mut counter = 1;
                //     for span in helper.spans {
                //         notes.push((span.0, format!("Increases cognitive complexity to {}", counter)));
                //         counter += 1;
                //     }
                //     span_notes_and_lint(
                //         cx,
                //         COGNITIVE_COMPLEXITY,
                //         span,
                //         &format!(
                //             "the function has a cognitive complexity of ({}/{})",
                //             rust_cc,
                //             self.limit.limit()
                //         ),
                //         notes);
                // } else {
                    span_help_and_lint(
                        cx,
                        COGNITIVE_COMPLEXITY,
                        span,
                        &format!(
                            "the function has a cognitive complexity of ({}/{})",
                            rust_cc,
                            self.limit.limit()
                        ),
                        "you could split it up into multiple smaller functions",
                    );
                // }
            }
        }
    }
}

impl<'a, 'tcx> LateLintPass<'a, 'tcx> for CognitiveComplexity {
    fn check_fn(
        &mut self,
        cx: &LateContext<'a, 'tcx>,
        _: intravisit::FnKind<'tcx>,
        _: &'tcx FnDecl,
        body: &'tcx Body,
        span: Span,
        hir_id: HirId,
    ) {
        let def_id = cx.tcx.hir().local_def_id(hir_id);
        if !cx.tcx.has_attr(def_id, sym!(test)) {
            self.check(cx, body, span);
        }
    }

    fn enter_lint_attrs(&mut self, cx: &LateContext<'a, 'tcx>, attrs: &'tcx [Attribute]) {
        self.limit.push_attrs(cx.sess(), attrs, "cognitive_complexity");
        self.verbosity.push_attrs(cx.sess(), attrs, "cognitive_complexity_verbosity");
    }
    fn exit_lint_attrs(&mut self, cx: &LateContext<'a, 'tcx>, attrs: &'tcx [Attribute]) {
        self.limit.pop_attrs(cx.sess(), attrs, "cognitive_complexity");
        self.verbosity.pop_attrs(cx.sess(), attrs, "cognitive_complexity_verbosity");
    }
}

#[derive(Copy, Clone, Eq, PartialEq)]
enum CCType {
    MatchArm,
    Divergence,
    Return,
    ShortCircuit, // && and ||
}

struct CCHelper<'a, 'tcx> {
    spans: Vec<(Span, CCType)>,
    cx: &'a LateContext<'a, 'tcx>,
}

impl<'a, 'tcx> Visitor<'tcx> for CCHelper<'a, 'tcx> {
    fn visit_expr(&mut self, e: &'tcx Expr) {
        match e.node {
            ExprKind::Match(_, ref arms, _) => {
                walk_expr(self, e);
                let arms_n: u64 = arms.iter().map(|arm| arm.pats.len() as u64).sum();
                if arms_n > 1 {
                    self.spans.push((e.span, CCType::MatchArm));
                }
            },
            ExprKind::Call(ref callee, _) => {
                walk_expr(self, e);
                let ty = self.cx.tables.node_type(callee.hir_id);
                match ty.sty {
                    ty::FnDef(..) | ty::FnPtr(_) => {
                        let sig = ty.fn_sig(self.cx.tcx);
                        if sig.skip_binder().output().sty == ty::Never {
                            self.spans.push((e.span, CCType::Divergence));
                        }
                    },
                    _ => (),
                }
            },
            ExprKind::Closure(.., _) => (),
            ExprKind::Binary(op, _, _) => {
                walk_expr(self, e);
                match op.node {
                    BinOpKind::And | BinOpKind::Or => self.spans.push((e.span, CCType::ShortCircuit)),
                    _ => (),
                }
            },
            // ExprKind::Ret(_) => self.returns.push(e.span),
            ExprKind::Ret(_) => self.spans.push((e.span, CCType::Return)),
            // ExprKind::Ret(_) => {
            //     if self.spans.iter().find(|(s, t)| s.source_equal(&e.span) && *t == CCType::Return).is_none() {
            //         self.spans.push((e.span, CCType::Return))
            //     }
            // },
            _ => walk_expr(self, e),
        }
    }
    fn nested_visit_map<'this>(&'this mut self) -> NestedVisitorMap<'this, 'tcx> {
        NestedVisitorMap::None
    }
}

#[cfg(feature = "debugging")]
#[allow(clippy::too_many_arguments)]
fn report_cc_bug(
    _: &LateContext<'_, '_>,
    cc: u64,
    narms: u64,
    div: u64,
    shorts: u64,
    returns: u64,
    span: Span,
    _: HirId,
) {
    span_bug!(
        span,
        "Clippy encountered a bug calculating cognitive complexity: cc = {}, arms = {}, \
         div = {}, shorts = {}, returns = {}. Please file a bug report.",
        cc,
        narms,
        div,
        shorts,
        returns
    );
}
#[cfg(not(feature = "debugging"))]
#[allow(clippy::too_many_arguments)]
fn report_cc_bug(
    cx: &LateContext<'_, '_>,
    cc: u64,
    narms: u64,
    div: u64,
    shorts: u64,
    returns: u64,
    span: Span,
    id: HirId,
) {
    if !is_allowed(cx, COGNITIVE_COMPLEXITY, id) {
        cx.sess().span_note_without_error(
            span,
            &format!(
                "Clippy encountered a bug calculating cognitive complexity \
                 (hide this message with `#[allow(cognitive_complexity)]`): \
                 cc = {}, arms = {}, div = {}, shorts = {}, returns = {}. \
                 Please file a bug report.",
                cc, narms, div, shorts, returns
            ),
        );
    }
}
