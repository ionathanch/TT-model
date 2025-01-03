import «TT-model».syntactics
import «TT-model».reduction
import «TT-model».typing
import «TT-model».candidates

open Term
open Nat

set_option autoImplicit false
set_option pp.fieldNotation false

variable [lc : LevelClass]

/-*------------------------------
  Renaming and weakening lemmas
------------------------------*-/

theorem semComp {ξ : ℕ → ℕ} {σ Γ Δ}
  (h : Δ ⊢ ξ ∶ Γ)
  (hζ : σ ⊨ Δ) :
  σ ∘ ξ ⊨ Γ := by
  intro x A mem
  rw [← substRename]
  exact hζ (ξ x) (rename ξ A) (h x A mem)

theorem semRename {ξ : ℕ → ℕ} {Γ Δ a A}
  (hξ : Δ ⊢ ξ ∶ Γ)
  (ha : Γ ⊨ a ∶ A) :
  Δ ⊨ rename ξ a ∶ rename ξ A := by
  intro σ hσ
  rw [substRename]; rw [substRename]
  exact ha (σ ∘ ξ) (semComp hξ hσ)

theorem semWeaken {Γ a A B}
  (ha : Γ ⊨ a ∶ A) :
  Γ ∷ B ⊨ rename succ a ∶ rename succ A := by
  exact semRename wRenameSucc ha

/-*---------------------------------------------
  Soundness of typing wrt the logical relation
---------------------------------------------*-/

theorem semWfCons {Γ A k} (hΓ : ⊨ Γ) (hA : Γ ⊨ A ∶ 𝒰 k) : ⊨ Γ ∷ A := by
  intros x A mem
  cases mem
  case here =>
    exists rename succ k
    exact semWeaken (A := 𝒰 k) hA
  case there x B mem =>
    let ⟨k, hB⟩ := hΓ x B mem
    exists rename succ k
    exact semWeaken (A := 𝒰 k) hB

theorem soundness {w} (h : Wtf w) :
  match w with
  | ⟨.wf, Γ⟩ => ⊨ Γ
  | ⟨.wt, ⟨Γ, a, A⟩⟩ => Γ ⊨ a ∶ A := by
  induction h using wtfInd
  case nil => intro x A mem; cases mem
  case cons k _ _ hΓ hA => exact semWfCons hΓ hA
  all_goals intro σ hσ
  case var x A wf mem h =>
    simp at h
    unfold semWf at h
    unfold semSubst at hσ
    let ⟨k, ih⟩ := h x A mem
    let ⟨_, _, h𝒰, hA⟩ := ih σ hσ
    let ⟨_, _, _, e⟩ := interps𝒰Inv h𝒰; subst e
    let ⟨_, hA⟩ := hA
    refine ⟨_, _, hA, hσ x A mem _ _ hA⟩
  case pi ihA ihB =>
    let ⟨_, _, h𝒰, hA⟩ := ihA σ hσ
    let ⟨_, _, ra, e⟩ := interps𝒰Inv h𝒰
    refine ⟨_, _, h𝒰, ?_⟩; subst e
    let ⟨PA, hA⟩ := hA
    constructor; apply interpsPi hA _ rfl
    intro x PAx; rw [← substUnion]
    let ⟨_, _, h𝒰, hB⟩ := ihB (x +: σ) (semSubstCons hA PAx hσ)
    let ⟨_, _, rb, e⟩ := interps𝒰Inv h𝒰
    subst e; rw [substRename] at rb
    let ⟨_, ra', rb'⟩ := confluence ra rb
    rw [parsLofInv ra'] at rb'
    injection (parsLofInv rb') with e
    simp_rw [e, hB]
  case abs ihpi ihb =>
    let ⟨_, _, h𝒰, hpi⟩ := ihpi σ hσ
    let ⟨_, _, _, e⟩ := interps𝒰Inv h𝒰
    subst e
    let ⟨_, hpi⟩ := hpi
    let ⟨_, hA, _, e⟩ := interpsPiInv hpi
    refine ⟨_, _, hpi, ?_⟩; subst e
    intro x Pb PAx hB; rw [← substUnion] at hB
    let ⟨_, _, hB', hb⟩ := ihb (x +: σ) (semSubstCons hA PAx hσ)
    rw [interpsDet hB hB']
    exact interpsBwdsP (parsβ σ) hB' hb
  case app ihb iha =>
    let ⟨_, _, hpi, hb⟩ := ihb σ hσ
    let ⟨_, PA, hA, ha⟩ := iha σ hσ
    let ⟨PA', hA', hB, e⟩ := interpsPiInv hpi
    rw [interpsDet hA hA'] at ha
    let ⟨_, hB⟩ := hB (subst σ _) ha
    subst e; rw [← substDist]
    exact ⟨_, _, hB, hb _ _ ha hB⟩
  case 𝒰 ih =>
    let ⟨_, P, hk, hj⟩ := ih σ hσ
    let ⟨k, rk, e⟩ := interpsLvlInv hk
    let ⟨ℓ, ltk⟩ := exists_gt k
    subst e
    refine ⟨ℓ, _, interpsBwds (pars𝒰 rk) (interps𝒰 ltk), ?_⟩
    cases hj
    case inl hj =>
      let ⟨j, rj, ltj⟩ := hj
      exact ⟨_, interpsBwds (pars𝒰 rj) (interps𝒰 ltj)⟩
    case inr wnej => sorry
  case mty ih =>
    let ⟨_, _, hj, hi⟩ := ih σ hσ
    let ⟨j, _, e⟩ := interpsLvlInv hj
    subst e
    cases hi
    case inl hi =>
      let ⟨i, ri, lt⟩ := hi
      exact ⟨j, _,
        interpsBwds (pars𝒰 ri) (interps𝒰 lt),
        ⟨_, interpsMty⟩⟩
    case inr wnei => sorry
  case exf b _ _ _ ihA ihb =>
    let ⟨k, _, hmty, hb⟩ := ihb σ hσ
    let ⟨_, _, h𝒰, hA⟩ := ihA σ hσ
    let ⟨_, _, _, e⟩ := interps𝒰Inv h𝒰; subst e
    let ⟨P, hA⟩ := hA
    let ⟨CRne, _⟩ := adequacy hA (exf (subst σ b))
    rw [interpsMtyInv hmty] at hb
    refine ⟨_, P, hA, CRne (wneExf hb)⟩
  case lvl k _ iha =>
    let ⟨_, P, hlvl, ha⟩ := iha σ hσ
    let ⟨ℓ, lt⟩ := exists_gt k
    refine ⟨ℓ, _, interps𝒰 lt, ?_⟩
    let ⟨_, _, e⟩ := interpsLvlInv hlvl
    subst e
    cases ha
    case inl ha =>
      let ⟨k, r, _⟩ := ha
      exact ⟨_, interpsBwds (parsLvl r) interpsLvl⟩
    case inr wnea => sorry
  case lof j k _ lt _ =>
    exact ⟨j, _, interpsLvl, Or.inl ⟨_, Pars.refl _, lt⟩⟩
  case trans j k _ _ ihj ihk =>
    let ⟨k, Pj, hk, hPj⟩ := ihk σ hσ
    let ⟨k, _, ePj⟩ := interpsLvlInv hk
    subst ePj
    let ⟨_, Pi, hj, hPi⟩ := ihj σ hσ
    let ⟨j', rj', ePi⟩ := interpsLvlInv hj
    subst ePi
    cases hPj
    case inr wnej => cases wneLof rj' wnej
    case inl hPj =>
    let ⟨j, rj, _⟩ := hPj
    let ⟨j'', rj, rj'⟩ := confluence rj rj'
    rw [parsLofInv rj] at rj'
    injection (parsLofInv rj') with e; subst e
    refine ⟨_, _, hk, ?_⟩
    cases hPi
    case inr wnei => exact Or.inr wnei
    case inl hPi =>
    let ⟨i, r, _⟩ := hPi
    refine Or.inl ⟨i, r, ?_⟩
    apply IsTrans.trans <;> assumption
  case conv e _ _ iha _ =>
    let ⟨_, _, hA, ha⟩ := iha σ hσ
    exact ⟨_, _, interpsConv (convSubst σ (eqvConv e)) hA, ha⟩
  case sub ihj ihA =>
    let ⟨_, Pj, h𝒰, hA⟩ := ihA σ hσ
    let ⟨_, _, rj, e⟩ := interps𝒰Inv h𝒰
    subst e
    let ⟨P, hA⟩ := hA
    let ⟨_, Pk, hk, hj⟩ := ihj σ hσ
    let ⟨k, rk, e⟩ := interpsLvlInv hk
    subst e
    cases hj
    case inr wnej => cases wneLof rj wnej
    case inl hj =>
    let ⟨_, rj', ltj'⟩ := hj
    let ⟨_, rj, rj'⟩ := confluence rj rj'
    rw [parsLofInv rj'] at rj
    injection (parsLofInv rj) with e; subst e
    let ⟨_, ltk⟩ := exists_gt k
    exact ⟨_, _,
      interpsBwds (pars𝒰 rk) (interps𝒰 ltk),
      ⟨_, interpsCumul ltj' hA⟩⟩

/-*-----------------------------------
  Existence of weak normal forms for
  well typed terms and their types
-----------------------------------*-/

theorem normalization {Γ} {a A : Term} (h : Γ ⊢ a ∶ A) : wnf a ∧ wnf A := by
  let ⟨_, _, hA, ha⟩ := soundness h var ?_
  . rw [substId] at ha hA
    let ⟨_, CRnf⟩ := adequacy hA a
    exact ⟨CRnf ha, interpsWnf hA⟩
  . intros x A _ i P hA
    rw [substId] at hA
    let ⟨CRne, _⟩ := adequacy hA (var x)
    exact CRne wneVar
