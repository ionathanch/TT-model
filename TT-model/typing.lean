import «TT-model».syntactics
import «TT-model».reduction

open Nat hiding all
open Term
open sort
open LevelClass

set_option autoImplicit false
set_option pp.fieldNotation false

variable [LevelClass]

/-*----------------------
  Definitional equality
----------------------*-/

section
set_option hygiene false
local infix:40 (priority := 1001) "≈" => Eqv -- override HasEquiv.Equiv

inductive Eqv : Term → Term → Prop where
  | β {b a} : app (abs b) a ≈ subst (a +: var) b
  | pi {a a' b b'} :
    a ≈ a' →
    b ≈ b' →
    -----------------
    pi a b ≈ pi a' b'
  | all {a a' b b'} :
    a ≈ a' →
    b ≈ b' →
    -----------------
    all a b ≈ all a' b'
  | abs {b b'} :
    b ≈ b' →
    --------------
    abs b ≈ abs b'
  | app {b b' a a'} :
    b ≈ b' →
    a ≈ a' →
    -------------------
    app b a ≈ app b' a'
  | exf {b b'} :
    b ≈ b' →
    --------------
    exf b ≈ exf b'
  | refl {a} : a ≈ a
  | sym {a b} :
    a ≈ b →
    -------
    b ≈ a
  | trans {a b c} :
    a ≈ b →
    b ≈ c →
    -------
    a ≈ c
end

infix:40 (priority := 1001) "≈" => Eqv

/-* Conversion is sound and complete with respect to definitional equality,
    making conversion an appropriate implementation of definitional equality *-/

theorem parEqv {a b} (r : a ⇒ b) : a ≈ b := by
  induction r
  case β ihb iha =>
    exact Eqv.trans (Eqv.app (Eqv.abs ihb) iha) Eqv.β
  all_goals constructor <;> assumption

theorem parsEqv {a b} (r : a ⇒⋆ b) : a ≈ b := by
  induction r
  case refl => constructor
  case trans r _ ih => exact (Eqv.trans (parEqv r) ih)

theorem convEqv {a b} : a ⇔ b → a ≈ b
  | ⟨_, rac, rbc⟩ => Eqv.trans (parsEqv rac) (Eqv.sym (parsEqv rbc))

theorem eqvConv {a b} (r : a ≈ b) : a ⇔ b := by
  induction r
  case β => apply_rules [parConv, Par.β, parRefl]
  case pi => apply_rules [convPi]
  case all => apply_rules [convAll]
  case abs => apply_rules [convAbs]
  case app => apply_rules [convApp]
  case exf => apply_rules [convExf]
  case refl => apply convRefl
  case sym => apply_rules [convSym]
  case trans => apply_rules [convTrans]

/-*-------------------------------------------------
  Context well-formedness and term well-typedness

  This is an encoding of a mutual inductive
  predicate as a single inductive,
  where I selects the original inductive
  (wf for the well-formedness judgement,
   wt for the well-typedness judgement),
  and idx provides the types of the indices
  for each judgement.
  The (w : I) and the idx i need to be paired up
  so that they can be generalized together
  during induction; generalizing over the w alone
  will result in an ill-typed idx w.
-------------------------------------------------*-/

inductive I | wf | wt𝒰 | wtℙ
open I

structure T where
  ctxt : Ctxt
  term : Term
  type : Term

def idx : I → Type
  | wf => Ctxt
  | wt𝒰 => T
  | wtℙ => T

section
set_option hygiene false
local notation:40 "⊢" Γ:40 => Wtf (Sigma.mk wf Γ)
local notation:40 Γ:41 "⊢" a:41 "∶" A:41 => Wtf (Sigma.mk wt𝒰 (T.mk Γ a A))
local notation:40 Γ:41 "⊢ₚ" a:41 "∶" A:41 => Wtf (Sigma.mk wtℙ (T.mk Γ a A))

inductive Wtf : (Σ w, idx w) → Prop where
  | nil : ⊢ ⬝
  | cons {Γ A k} :
    ⊢ Γ →
    Γ ⊢ A ∶ 𝒰 k →
    --------------
    ⊢ Γ ∷ A
  | icons {Γ A} :
    ⊢ Γ →
    Γ ⊢ A ∶ ℙ →
    --------------
    ⊢ Γ ∷ A
  | var {Γ x A} :
    ⊢ Γ →
    Γ ∋ x ∶ A ∶ 𝒰 →
    ----------------
    Γ ⊢ var x ∶ A
  | ivar {Γ x A} :
    ⊢ Γ →
    Γ ∋ x ∶ A ∶ ℙ →
    ---------------
    Γ ⊢ₚ var x ∶ A
  | 𝒰 {Γ j k} :
    j < k →
    ---------------
    Γ ⊢ 𝒰 j ∶ 𝒰 k
  | pi {Γ A B k} :
    Γ ⊢ A ∶ 𝒰 k →
    Γ ∷ A ⊢ B ∶ 𝒰 k →
    ------------------
    Γ ⊢ pi A B ∶ 𝒰 k
  | abs {Γ A B b k} :
    Γ ⊢ pi A B ∶ 𝒰 k →
    Γ ∷ A ⊢ b ∶ B →
    -------------------
    Γ ⊢ abs b ∶ pi A B
  | app {Γ A B b a} :
    Γ ⊢ b ∶ pi A B →
    Γ ⊢ a ∶ A →
    --------------------------------
    Γ ⊢ app b a ∶ subst (a +: var) B
  | ℙ {Γ} :
    ⊢ Γ →
    --------------
    Γ ⊢ ℙ ∶ 𝒰 «0»
  | all {Γ A B k} :
    Γ ⊢ A ∶ 𝒰 k →
    Γ ∷ A ⊢ B ∶ ℙ →
    ---------------
    Γ ⊢ all A B ∶ ℙ
  | iabs {Γ A B b k} :
    Γ ⊢ A ∶ 𝒰 k →
    Γ ∷ A ⊢ₚ b ∶ B →
    --------------------
    Γ ⊢ₚ abs b ∶ all A B
  | iapp {Γ A B b a} :
    Γ ⊢ₚ b ∶ all A B →
    Γ ⊢ a ∶ A →
    ---------------------------------
    Γ ⊢ₚ app b a ∶ subst (a +: var) B
  | mty {Γ} :
    -----------
    Γ ⊢ mty ∶ ℙ
  | exf {Γ A b k} :
    Γ ⊢ A ∶ 𝒰 k →
    Γ ⊢ₚ b ∶ mty →
    --------------
    Γ ⊢ exf b ∶ A
  | iexf {Γ A b} :
    Γ ⊢ A ∶ ℙ →
    Γ ⊢ₚ b ∶ mty →
    --------------
    Γ ⊢ₚ exf b ∶ A
  | conv {Γ A B a k} :
    A ≈ B →
    Γ ⊢ a ∶ A →
    Γ ⊢ B ∶ 𝒰 k →
    --------------
    Γ ⊢ a ∶ B
  | iconv {Γ A B a} :
    A ≈ B →
    Γ ⊢ₚ a ∶ A →
    Γ ⊢ B ∶ ℙ →
    -----------
    Γ ⊢ₚ a ∶ B
  | sub {Γ j k A} :
    j < k →
    Γ ⊢ A ∶ 𝒰 j →
    --------------
    Γ ⊢ A ∶ 𝒰 k
  | isub {Γ A k} :
    Γ ⊢ A ∶ ℙ →
    ------------
    Γ ⊢ A ∶ 𝒰 k
end

notation:40 "⊢" Γ:40 => Wtf (Sigma.mk wf Γ)
notation:40 Γ:41 "⊢" a:41 "∶" A:41 => Wtf (Sigma.mk wt𝒰 (T.mk Γ a A))
notation:40 Γ:41 "⊢ₚ" a:41 "∶" A:41 => Wtf (Sigma.mk wtℙ (T.mk Γ a A))

theorem wtfApp {Γ A B B' b a}
  (hpi : Γ ⊢ b ∶ pi A B)
  (ha : Γ ⊢ a ∶ A)
  (eB : B' = subst (a +: var) B) :
  Γ ⊢ app b a ∶ B' := by
  subst eB; constructor <;> assumption
