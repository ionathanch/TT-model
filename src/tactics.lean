import Lean.Elab.Tactic.Basic

set_option autoImplicit false
set_option pp.fieldNotation false

/-- Return `true` if the expression is a function type
    whose first explicit argument is an equality. -/
def firstArgEq? : Lean.Expr → Bool
  | .forallE _ bType _ .default =>
    Lean.Expr.isEq bType
  | .forallE _ _ body _ =>
    firstArgEq? body
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
