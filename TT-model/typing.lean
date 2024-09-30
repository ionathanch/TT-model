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
  case 𝒰 => apply_rules [conv𝒰]
  case pi => apply_rules [convPi]
  case abs => apply_rules [convAbs]
  case app => apply_rules [convApp]
  case exf => apply_rules [convExf]
  case lvl => apply_rules [convLvl]
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

/-*---------------------------------------
  Better constructors + inversion lemmas
---------------------------------------*-/

theorem wtfApp {Γ A B B' b a}
  (hpi : Γ ⊢ b ∶ pi A B)
  (ha : Γ ⊢ a ∶ A)
  (eB : B' = subst (a +: var) B) :
  Γ ⊢ app b a ∶ B' := by
  subst eB; constructor <;> assumption

theorem wtf𝒰Inv {Γ j 𝒰'}
  (h : Γ ⊢ 𝒰 j ∶ 𝒰') :
  ∃ k, 𝒰 k ≈ 𝒰' := by
  generalize e : @Sigma.mk I idx I.wt ⟨Γ, 𝒰 j, 𝒰'⟩ = t at h
  induction h generalizing Γ j 𝒰'
  all_goals injection e with eI e; injection eI
  all_goals injection e with eCtxt eTerm eType; subst eCtxt; subst eType
  all_goals first | contradiction | injection eTerm | subst eTerm
  case 𝒰 | sub => exact ⟨_, Eqv.refl⟩
  case trans ih =>
    let ⟨_, e⟩ := ih rfl
    cases convLvl𝒰 (convSym (eqvConv e))
  case conv e₁ _ _ _ ih =>
    let ⟨_, e₂⟩ := ih rfl
    exact ⟨_, Eqv.trans e₂ e₁⟩

theorem wtfPiInvA {Γ A B 𝒰'}
  (h : Γ ⊢ pi A B ∶ 𝒰') :
  ∃ j, Γ ⊢ A ∶ 𝒰 j := by
  generalize e : @Sigma.mk I idx I.wt ⟨Γ, pi A B, 𝒰'⟩ = t at h
  induction h generalizing Γ A B 𝒰'
  all_goals injection e with eI e; injection eI
  all_goals injection e with eCtxt eTerm eType; subst eCtxt; subst eType
  all_goals first | contradiction | injection eTerm | subst eTerm
  case pi k _ _ _ _ eA eB => subst eA; subst eB; exists k
  case trans ih | conv ih | sub ih => apply ih rfl

theorem wtfPiInvB {Γ A B 𝒰'}
  (h : Γ ⊢ pi A B ∶ 𝒰') :
  ∃ j, Γ ∷ A ⊢ B ∶ 𝒰 j := by
  generalize e : @Sigma.mk I idx I.wt ⟨Γ, pi A B, 𝒰'⟩ = t at h
  induction h generalizing Γ A B 𝒰'
  all_goals injection e with eI e; injection eI
  all_goals injection e with eCtxt eTerm eType; subst eCtxt; subst eType
  all_goals first | contradiction | injection eTerm | subst eTerm
  case pi k _ _ _ _ eA eB => subst eA; subst eB; exists rename succ k
  case trans ih | conv ih | sub ih => apply ih rfl

theorem wtfPiInv𝒰 {Γ A B 𝒰'}
  (h : Γ ⊢ pi A B ∶ 𝒰') :
  ∃ j, 𝒰 j ≈ 𝒰' := by
  generalize e : @Sigma.mk I idx I.wt ⟨Γ, pi A B, 𝒰'⟩ = t at h
  induction h generalizing Γ A B 𝒰'
  all_goals injection e with eI e; injection eI
  all_goals injection e with eCtxt eTerm eType; subst eCtxt; subst eType
  all_goals first | contradiction | injection eTerm | subst eTerm
  case pi | sub => exact ⟨_, Eqv.refl⟩
  case trans ih =>
    let ⟨_, e⟩ := ih rfl
    cases convLvl𝒰 (convSym (eqvConv e))
  case conv e₁ _ _ _ ih =>
    let ⟨_, e₂⟩ := ih rfl
    exact ⟨_, Eqv.trans e₂ e₁⟩

theorem wtfAbsInv {Γ b C}
  (h : Γ ⊢ abs b ∶ C) :
  ∃ A B, Γ ∷ A ⊢ b ∶ B ∧ pi A B ≈ C := by
  generalize e : @Sigma.mk I idx I.wt ⟨Γ, abs b, C⟩ = t at h
  induction h generalizing Γ b C
  all_goals injection e with eI e; injection eI
  all_goals injection e with eCtxt eTerm eType; subst eCtxt; subst eType
  all_goals first | contradiction | injection eTerm | subst eTerm
  case abs hb _ _ e => subst e; exact ⟨_, _, hb, Eqv.refl⟩
  case trans ih =>
    let ⟨_, _, _, e⟩ := ih rfl
    have := convLvlPi (convSym (eqvConv e))
    contradiction
  case conv DC _ _ _ ih =>
    let ⟨A, B, hb, ABD⟩ := ih rfl
    exact ⟨A, B, hb, Eqv.trans ABD DC⟩
  case sub ih =>
    let ⟨_, _, _, e⟩ := ih rfl
    have := conv𝒰Pi (convSym (eqvConv e))
    contradiction

theorem wtfMtyInv {Γ 𝒰'}
  (h : Γ ⊢ mty ∶ 𝒰') :
  ∃ k, 𝒰 k ≈ 𝒰' := by
  generalize e : @Sigma.mk I idx I.wt ⟨Γ, mty, 𝒰'⟩ = t at h
  induction h generalizing Γ 𝒰'
  all_goals injection e with eI e; injection eI
  all_goals injection e with eCtxt eTerm eType; subst eCtxt; subst eType
  all_goals first | contradiction | injection eTerm | subst eTerm
  case mty | sub => exact ⟨_, Eqv.refl⟩
  case trans ih =>
    let ⟨_, e⟩ := ih rfl
    cases convLvl𝒰 (convSym (eqvConv e))
  case conv e₁ _ _ _ ih =>
    let ⟨_, e₂⟩ := ih rfl
    exact ⟨_, Eqv.trans e₂ e₁⟩

theorem wtfLvlInv {Γ a 𝒰'}
  (h : Γ ⊢ lvl a ∶ 𝒰') :
  ∃ b k, Γ ⊢ a ∶ lvl b ∧ 𝒰 k ≈ 𝒰' := by
  generalize e : @Sigma.mk I idx I.wt ⟨Γ, lvl a, 𝒰'⟩ = t at h
  induction h generalizing Γ a 𝒰'
  all_goals injection e with eI e; injection eI
  all_goals injection e with eCtxt eTerm eType; subst eCtxt; subst eType
  all_goals first | contradiction | injection eTerm | subst eTerm
  case lvl ha _ e => subst e; exact ⟨_, _, ha, Eqv.refl⟩
  case trans ih =>
    let ⟨_, _, _, e⟩ := ih rfl
    cases convLvl𝒰 (convSym (eqvConv e))
  case conv e₁ _ _ _ ih =>
    let ⟨b, _, ha, e₂⟩ := ih rfl
    exact ⟨b, _, ha, Eqv.trans e₂ e₁⟩
  case sub ih =>
    let ⟨b, _, ha, _⟩ := ih rfl
    exact ⟨b, _, ha, Eqv.refl⟩

theorem wtfLofInv {Γ j 𝒰'}
  (h : Γ ⊢ lof j ∶ 𝒰') :
  ∃ k, lvl k ≈ 𝒰' := by
  generalize e : @Sigma.mk I idx I.wt ⟨Γ, lof j, 𝒰'⟩ = t at h
  induction h generalizing Γ j 𝒰'
  all_goals injection e with eI e; injection eI
  all_goals injection e with eCtxt eTerm eType; subst eCtxt; subst eType
  all_goals first | contradiction | injection eTerm | subst eTerm
  case lof e => subst e; exact ⟨_, Eqv.refl⟩
  case trans => exact ⟨_, Eqv.refl⟩
  case conv e₁ _ _ _ ih =>
    let ⟨_, e₂⟩ := ih rfl
    exact ⟨_, Eqv.trans e₂ e₁⟩
  case sub ih =>
    let ⟨_, e⟩ := ih rfl
    cases convLvl𝒰 (eqvConv e)

theorem wtWf {Γ} {a A : Term} (h : Γ ⊢ a ∶ A) : ⊢ Γ := by
  generalize e : @Sigma.mk I idx I.wt ⟨Γ, a, A⟩ = t at h
  induction h generalizing Γ a A
  all_goals injection e with eI e; injection eI
  all_goals injection e with eCtxt eTerm eType;
            subst eCtxt; subst eTerm; subst eType
  all_goals apply_rules

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
