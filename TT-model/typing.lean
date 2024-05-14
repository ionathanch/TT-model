import «TT-model».syntactics
import «TT-model».reduction

open Term
open Ctxt (nil)

set_option autoImplicit false

/-*----------------------
  Definitional equality
----------------------*-/

inductive Eqv : Term → Term → Prop where
  | β {b a} : Eqv (app (abs b) a) (subst (a +: var) b)
  | pi {a a' b b'} :
    Eqv a a' →
    Eqv b b' →
    -----------------------
    Eqv (pi a b) (pi a' b')
  | abs {b b'} :
    Eqv b b' →
    --------------------
    Eqv (abs b) (abs b')
  | app {b b' a a'} :
    Eqv b b' →
    Eqv a a' →
    -------------------------
    Eqv (app b a) (app b' a')
  | exf {b b'} :
    Eqv b b' →
    --------------------
    Eqv (exf b) (exf b')
  | refl {a} : Eqv a a
  | sym {a b} :
    Eqv a b →
    ---------
    Eqv b a
  | trans {a b c} :
    Eqv a b →
    Eqv b c →
    ---------
    Eqv a c
infix:40 "≈" => Eqv

/-* Conversion is sound and complete with respect to definitional equality,
    making conversion an appropriate implementation of definitional equality *-/

theorem parEqv {a b} (r : a ⇒ b) : a ≈ b := by
  induction r <;> try (constructor <;> assumption)
  case β ihb iha =>
    apply Eqv.trans
    exact (Eqv.app (Eqv.abs ihb) iha)
    apply Eqv.β

theorem parsEqv {a b} (r : a ⇒⋆ b) : a ≈ b := by
  induction r
  case refl => constructor
  case trans r _ ih => exact (Eqv.trans (parEqv r) ih)

theorem convEqv {a b} : a ⇔ b → a ≈ b
  | ⟨_, rac, rbc⟩ => by
    apply Eqv.trans
    apply parsEqv rac
    apply Eqv.sym
    apply parsEqv rbc

theorem eqvConv {a b} (r : a ≈ b) : a ⇔ b := by
  induction r
  case β => apply parConv; apply Par.β <;> apply parRefl
  case pi => apply convPi <;> assumption
  case abs => apply convAbs; assumption
  case app => apply convApp <;> assumption
  case exf => apply convExf; assumption
  case refl => apply convRefl
  case sym => apply convSym; assumption
  case trans => apply convTrans <;> assumption

/-*-------------------------------------------------
  Context well-formedness and term well-typedness
-------------------------------------------------*-/

mutual
inductive Wf : Ctxt → Prop where
  | nil : Wf nil
  | cons {Γ A k} :
    Wf Γ →
    Wt Γ A (𝒰 k) →
    ---------------
    Wf (Γ ∷ A)

inductive Wt : Ctxt → Term → Term → Prop where
  | var {Γ x A} :
    Wf Γ →
    In x A Γ →
    --------------
    Wt Γ (var x) A
  | 𝒰 {Γ j k} :
    Wf Γ →
    j < k →
    Wt Γ (𝒰 j) (𝒰 k)
  | pi {Γ A B k} :
    Wt Γ A (𝒰 k) →
    Wt (Γ ∷ A) B (𝒰 k) →
    ---------------------
    Wt Γ (pi A B) (𝒰 k)
  | abs {Γ A B b k} :
    Wt Γ (pi A B) (𝒰 k) →
    Wt (Γ ∷ A) b B →
    ----------------------
    Wt Γ (abs b) (pi A B)
  | app {Γ A B b a} :
    Wt Γ b (pi A B) →
    Wt Γ a A →
    -----------------------------------
    Wt Γ (app b a) (subst (a +: var) B)
  | mty {Γ k} :
    Wf Γ →
    ---------------
    Wt Γ mty (𝒰 k)
  | exf {Γ A b k} :
    Wt Γ A (𝒰 k) →
    Wt Γ b mty →
    --------------
    Wt Γ (exf b) A
  | conv {Γ A B a k} :
    A ≈ B →
    Wt Γ a A →
    Wt Γ B (𝒰 k) →
    ------------------
    Wt Γ a B
end

prefix:95 "⊢" => Wf
notation:40 Γ "⊢" a "⦂" A => Wt Γ a A
