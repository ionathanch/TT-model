import «src».reduction

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
  | β {b a c} : app (abs c b) a ≈ subst (a +: var) b
  | 𝒰 {a a'} :
    a ≈ a' →
    -----------
    𝒰 a ≈ 𝒰 a'
  | pi {a a' b b'} :
    a ≈ a' →
    b ≈ b' →
    -----------------
    pi a b ≈ pi a' b'
  | abs {a a' b b'} :
    a ≈ a' →
    b ≈ b' →
    -------------------
    abs a b ≈ abs a' b'
  | app {b b' a a'} :
    b ≈ b' →
    a ≈ a' →
    -------------------
    app b a ≈ app b' a'
  | exf {a a' b b'} :
    a ≈ a' →
    b ≈ b' →
    -------------------
    exf a b ≈ exf a' b'
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
    exact Eqv.trans (Eqv.app (Eqv.abs Eqv.refl ihb) iha) Eqv.β
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
-------------------------------------------------*-/

section
set_option hygiene false
local notation:40 "⊢" Γ:40 => Wf Γ
local notation:40 Γ:41 "⊢" a:41 "∶" A:41 => Wt Γ a A

mutual
inductive Wf : Ctxt → Prop where
  | nil : ⊢ ⬝
  | cons {Γ A k} :
    ⊢ Γ →
    Γ ⊢ A ∶ 𝒰 k →
    --------------
    ⊢ Γ ∷ A

inductive Wt : Ctxt → Term → Term → Prop where
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
    Γ ⊢ A ∶ 𝒰 k →
    Γ ∷ A ⊢ b ∶ B →
    --------------------
    Γ ⊢ abs A b ∶ pi A B
  | app {Γ A B b a} :
    Γ ⊢ b ∶ pi A B →
    Γ ⊢ a ∶ A →
    --------------------------------
    Γ ⊢ app b a ∶ subst (a +: var) B
  | mty {Γ j k} :
    Γ ⊢ 𝒰 j ∶ 𝒰 k →
    -----------------
    Γ ⊢ mty ∶ 𝒰 j
  | exf {Γ A b k} :
    Γ ⊢ A ∶ 𝒰 k →
    Γ ⊢ b ∶ mty →
    ---------------
    Γ ⊢ exf A b ∶ A
  | lvl {Γ a b j k} :
    Γ ⊢ a ∶ lvl b →
    Γ ⊢ 𝒰 j ∶ 𝒰 k →
    ----------------------
    Γ ⊢ lvl a ∶ 𝒰 j
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
end

notation:40 "⊢" Γ:40 => Wf Γ
notation:40 Γ:41 "⊢" a:41 "∶" A:41 => Wt Γ a A

/-*------------------------------
  Explicit induction principles
------------------------------*-/

def wtInd {motive} :=
  @Wt.rec _ (λ _ _ ↦ True) motive (by simp) (by simp)

theorem wtfInd (Q : ∀ {Γ}, ⊢ Γ → Prop) (P : ∀ {Γ} {a A : Term}, Γ ⊢ a ∶ A → Prop)
  (nil : Q Wf.nil)
  (cons : ∀ {Γ A k}
    (wf : ⊢ Γ)
    (h : Γ ⊢ A ∶ 𝒰 k),
    Q wf → P h → Q (Wf.cons wf h))
  (var : ∀ {Γ x A}
    (wf : ⊢ Γ)
    (mem : Γ ∋ x ∶ A),
    Q wf → P (Wt.var wf mem))
  (𝒰 : ∀ {Γ j k}
    (h : Γ ⊢ j ∶ lvl k),
    P h → P (Wt.𝒰 h))
  (pi : ∀ {Γ A B k}
    (hA : Γ ⊢ A ∶ Term.𝒰 k)
    (hB : Γ ∷ A ⊢ B ∶ Term.𝒰 (rename succ k)),
    P hA → P hB → P (Wt.pi hA hB))
  (abs : ∀ {Γ A B b k}
    (hpi : Γ ⊢ Term.pi A B ∶ Term.𝒰 k)
    (hA : Γ ⊢ A ∶ Term.𝒰 k)
    (hb : Γ ∷ A ⊢ b ∶ B),
    P hpi → P hA → P hb → P (Wt.abs hpi hA hb))
  (app : ∀ {Γ A B b a}
    (hb : Γ ⊢ b ∶ Term.pi A B)
    (ha : Γ ⊢ a ∶ A),
    P hb → P ha → P (Wt.app hb ha))
  (mty : ∀ {Γ j k}
    (h : Γ ⊢ Term.𝒰 j ∶ Term.𝒰 k),
    P h → P (Wt.mty h))
  (exf : ∀ {Γ A b k}
    (hA : Γ ⊢ A ∶ Term.𝒰 k)
    (hb : Γ ⊢ b ∶ Term.mty),
    P hA → P hb → P (Wt.exf hA hb))
  (lvl : ∀ {Γ a b j k}
    (ha : Γ ⊢ a ∶ lvl b)
    (hj : Γ ⊢ Term.𝒰 j ∶ Term.𝒰 k),
    P ha → P hj → P (Wt.lvl ha hj))
  (lof : ∀ {Γ j k}
    (wf : ⊢ Γ)
    (lt : j < k),
    Q wf → P (Wt.lof wf lt))
  (trans : ∀ {Γ i j k}
    (hi : Γ ⊢ i ∶ Term.lvl j)
    (hj : Γ ⊢ j ∶ Term.lvl k),
    P hi → P hj → P (Wt.trans hi hj))
  (conv : ∀ {Γ A B a k}
    (e : A ≈ B)
    (ha : Γ ⊢ a ∶ A)
    (hB : Γ ⊢ B ∶ Term.𝒰 k),
    P ha → P hB → P (Wt.conv e ha hB))
  (sub : ∀ {Γ j k A}
    (hj : Γ ⊢ j ∶ Term.lvl k)
    (hA : Γ ⊢ A ∶ Term.𝒰 j),
    P hj → P hA → P (Wt.sub hj hA))
  : (∀ {Γ} (wf : ⊢ Γ), Q wf) ∧ (∀ {Γ} {a A : Term} (wt : Γ ⊢ a ∶ A), P wt) :=
  ⟨@Wf.rec _ @Q @P nil cons var 𝒰 pi abs app mty exf lvl lof trans conv sub,
   @Wt.rec _ @Q @P nil cons var 𝒰 pi abs app mty exf lvl lof trans conv sub⟩

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
  generalize e : 𝒰 j = t at h
  induction h using wtInd
  all_goals injections <;> subst_eqs <;> specialize_rfls
  case 𝒰 | sub => exact ⟨_, Eqv.refl⟩
  case trans ih =>
    let ⟨_, e⟩ := ih
    cases convLvl𝒰 (convSym (eqvConv e))
  case conv e₁ _ _ _ ih =>
    let ⟨_, e₂⟩ := ih
    exact ⟨_, Eqv.trans e₂ e₁⟩

theorem wtfPiInvA𝒰 {Γ A B 𝒰'}
  (h : Γ ⊢ pi A B ∶ 𝒰') :
  ∃ j, Γ ⊢ A ∶ 𝒰 j ∧ 𝒰 j ≈ 𝒰' := by
  generalize e : pi A B = t at h
  induction h using wtInd
  all_goals injections <;> subst_eqs <;> specialize_rfls
  case pi j hA _ _ _ => exact ⟨j, hA, Eqv.refl⟩
  case trans ih =>
    let ⟨_, _, e⟩ := ih
    cases (convLvl𝒰 (convSym (eqvConv e)))
  case conv e₁ _ _ _ ih =>
    let ⟨_, hA, e₂⟩ := ih
    exact ⟨_, hA, Eqv.trans e₂ e₁⟩
  case sub hj _ _ ih =>
    let ⟨_, hA, e⟩ := ih
    exact ⟨_, Wt.sub hj (Wt.conv e hA (Wt.𝒰 hj)), Eqv.refl⟩

theorem wtfPiInvA {Γ A B 𝒰'}
  (h : Γ ⊢ pi A B ∶ 𝒰') :
  ∃ j, Γ ⊢ A ∶ 𝒰 j := by
  let ⟨j, hA, _⟩ := wtfPiInvA𝒰 h
  exact ⟨j, hA⟩

theorem wtfPiInvB {Γ A B 𝒰'}
  (h : Γ ⊢ pi A B ∶ 𝒰') :
  ∃ j, Γ ∷ A ⊢ B ∶ 𝒰 j := by
  generalize e : pi A B = t at h
  induction h using wtInd
  all_goals injections <;> subst_eqs <;> specialize_rfls
  case pi k _ _ _ _ => exists rename succ k
  all_goals assumption

theorem wtfPiInv𝒰 {Γ A B 𝒰'}
  (h : Γ ⊢ pi A B ∶ 𝒰') :
  ∃ j, 𝒰 j ≈ 𝒰' := by
  let ⟨j, _, e⟩ := wtfPiInvA𝒰 h
  exact ⟨j, e⟩

theorem wtfAbsInv {Γ A' b C}
  (h : Γ ⊢ abs A' b ∶ C) :
  ∃ A B, Γ ∷ A ⊢ b ∶ B ∧ A ≈ A' ∧ pi A B ≈ C := by
  generalize e : abs A' b = t at h
  induction h using wtInd
  all_goals injections <;> subst_eqs <;> specialize_rfls
  case abs hb _ => exact ⟨_, _, hb, Eqv.refl, Eqv.refl⟩
  case trans ih =>
    let ⟨_, _, _, _, eC⟩ := ih
    cases convLvlPi (convSym (eqvConv eC))
  case conv DC _ _ _ ih =>
    let ⟨A, B, hb, AA', ABD⟩ := ih
    exact ⟨A, B, hb, AA', Eqv.trans ABD DC⟩
  case sub ih =>
    let ⟨_, _, _, _, e⟩ := ih
    cases conv𝒰Pi (convSym (eqvConv e))

theorem wtfMtyInv {Γ 𝒰'}
  (h : Γ ⊢ mty ∶ 𝒰') :
  ∃ k, 𝒰 k ≈ 𝒰' := by
  generalize e : mty = t at h
  induction h using wtInd
  all_goals injections <;> subst_eqs <;> specialize_rfls
  case mty | sub => exact ⟨_, Eqv.refl⟩
  case trans ih =>
    let ⟨_, e⟩ := ih
    cases convLvl𝒰 (convSym (eqvConv e))
  case conv e₁ _ _ _ ih =>
    let ⟨_, e₂⟩ := ih
    exact ⟨_, Eqv.trans e₂ e₁⟩

theorem wtfLvlInv {Γ a 𝒰'}
  (h : Γ ⊢ lvl a ∶ 𝒰') :
  ∃ b k, Γ ⊢ a ∶ lvl b ∧ 𝒰 k ≈ 𝒰' := by
  generalize e : lvl a = t at h
  induction h using wtInd
  all_goals injections <;> subst_eqs <;> specialize_rfls
  case lvl ha _ => exact ⟨_, _, ha, Eqv.refl⟩
  case trans ih =>
    let ⟨_, _, _, e⟩ := ih
    cases convLvl𝒰 (convSym (eqvConv e))
  case conv e₁ _ _ _ ih =>
    let ⟨b, _, ha, e₂⟩ := ih
    exact ⟨b, _, ha, Eqv.trans e₂ e₁⟩
  case sub ih =>
    let ⟨b, _, ha, _⟩ := ih
    exact ⟨b, _, ha, Eqv.refl⟩

theorem wtfLofInv {Γ j 𝒰'}
  (h : Γ ⊢ lof j ∶ 𝒰') :
  ∃ k, lvl k ≈ 𝒰' := by
  generalize e : lof j = t at h
  induction h using wtInd
  all_goals injections <;> subst_eqs <;> specialize_rfls
  case lof | trans => exact ⟨_, Eqv.refl⟩
  case conv e₁ _ _ _ ih =>
    let ⟨_, e₂⟩ := ih
    exact ⟨_, Eqv.trans e₂ e₁⟩
  case sub ih =>
    let ⟨_, e⟩ := ih
    cases convLvl𝒰 (eqvConv e)

theorem wtWf {Γ} {a A : Term} (h : Γ ⊢ a ∶ A) : ⊢ Γ := by
  induction h using wtInd <;> assumption
