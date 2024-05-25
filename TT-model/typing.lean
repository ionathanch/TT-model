import «TT-model».syntactics
import «TT-model».reduction

open Nat
open Term

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
  | 𝒰 {a a'} :
    a ≈ a' →
    -----------
    𝒰 a ≈ 𝒰 a'
  | pi {a a' b b'} :
    a ≈ a' →
    b ≈ b' →
    -----------------
    pi a b ≈ pi a' b'
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
  | lvl {a a'} :
    a ≈ a' →
    -----------
    lvl a ≈ lvl a'
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
  case 𝒰 => apply conv𝒰; assumption
  case pi => apply convPi <;> assumption
  case abs => apply convAbs; assumption
  case app => apply convApp <;> assumption
  case exf => apply convExf; assumption
  case lvl => apply convLvl; assumption
  case refl => apply convRefl
  case sym => apply convSym; assumption
  case trans => apply convTrans <;> assumption

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

inductive I : Type where
  | wf : I
  | wt : I
open I

structure T where
  ctxt : Ctxt
  term : Term
  type : Term

def idx : I → Type
  | wf => Ctxt
  | wt => T

section
set_option hygiene false
local notation:40 "⊢" Γ:40 => Wtf (Sigma.mk wf Γ)
local notation:40 Γ:41 "⊢" a:41 "∶" A:41 => Wtf (Sigma.mk wt (T.mk Γ a A))

inductive Wtf : (Σ w, idx w) → Prop where
  | nil : ⊢ ⬝
  | cons {Γ A k} :
    ⊢ Γ →
    Γ ⊢ A ∶ 𝒰 k →
    --------------
    ⊢ Γ ∷ A
  | var {Γ x A} :
    ⊢ Γ →
    Γ ∋ x ∶ A →
    -------------
    Γ ⊢ var x ∶ A
  | 𝒰 {Γ j k} :
    Γ ⊢ j ∶ lvl k →
    ---------------
    Γ ⊢ 𝒰 j ∶ 𝒰 k
  | pi {Γ A B k} :
    Γ ⊢ A ∶ 𝒰 k →
    Γ ∷ A ⊢ B ∶ 𝒰 (rename succ k) →
    --------------------------------
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
  | mty {Γ j k} :
    Γ ⊢ j ∶ lvl k →
    ---------------
    Γ ⊢ mty ∶ 𝒰 j
  | exf {Γ A b k} :
    Γ ⊢ A ∶ 𝒰 k →
    Γ ⊢ b ∶ mty →
    -------------
    Γ ⊢ exf b ∶ A
  | lvl {Γ a b k} :
    Γ ⊢ a ∶ lvl b →
    ----------------------
    Γ ⊢ lvl a ∶ 𝒰 (lof k)
  | lof {Γ j k} :
    ⊢ Γ →
    j < k →
    -----------------------
    Γ ⊢ lof j ∶ lvl (lof k)
  | trans {Γ i j k} :
    Γ ⊢ i ∶ lvl j →
    Γ ⊢ j ∶ lvl k →
    ---------------
    Γ ⊢ i ∶ lvl k
  | conv {Γ A B a k} :
    A ≈ B →
    Γ ⊢ a ∶ A →
    Γ ⊢ B ∶ 𝒰 k →
    --------------
    Γ ⊢ a ∶ B
  | sub {Γ j k A} :
    Γ ⊢ j ∶ lvl k →
    Γ ⊢ A ∶ 𝒰 j →
    ---------------
    Γ ⊢ A ∶ 𝒰 k
end

notation:40 "⊢" Γ:40 => Wtf (Sigma.mk wf Γ)
notation:40 Γ:41 "⊢" a:41 "∶" A:41 => Wtf (Sigma.mk wt (T.mk Γ a A))

theorem wtfApp {Γ A B B' b a}
  (hpi : Γ ⊢ b ∶ pi A B)
  (ha : Γ ⊢ a ∶ A)
  (eB : B' = subst (a +: var) B) :
  Γ ⊢ app b a ∶ B' := by
  subst eB; apply Wtf.app <;> assumption

/-*---------------------------------------------
  Lean currently doesn't support induction on
  mutual inductives, nor structural recursion
  on inductive predicates in Prop.
  Put the below back when it does.

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
notation:40 Γ "⊢" a "∶" A => Wt Γ a A
---------------------------------------------*-/
