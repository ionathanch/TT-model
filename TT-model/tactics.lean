import Lean.Elab.Tactic.Basic

set_option autoImplicit false
set_option pp.fieldNotation false

/-- The `inj_subst` tactic finds an equality
    and either inverts it by `injection` or uses it by `subst`,
    repeating until no more equalities are found. -/
macro "inj_subst" : tactic =>
  `(tactic| repeat (rename _ = _ => e; first | injection e | subst e))

/-- Return `true` if the expression is a function type
    whose first explicit argument is an equality. -/
def firstArgEq? : Lean.Expr → Bool
  | .forallE _ (.app (.app (.app (.const `Eq _) _) _) _) _ binfo =>
    Lean.BinderInfo.isExplicit binfo
  | .forallE _ _ bbody binfo =>
    Lean.BinderInfo.isImplicit binfo && firstArgEq? bbody
  | _ => false

/-- The `specialize_rfls` tactic tries to specialize all hypotheses
    whose first explicit argument is an equality with `rfl`. -/
elab "specialize_rfls" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let ctx ← Lean.MonadLCtx.getLCtx
    ctx.forM fun decl: Lean.LocalDecl => do
      let declType ← Lean.Meta.inferType decl.toExpr
      if firstArgEq? declType then
        Lean.Elab.Tactic.evalTactic
          (← `(tactic| try specialize $(Lean.mkIdent decl.userName) rfl))
