import «src».typing
import «src».semantics

open Term

set_option autoImplicit false
set_option pp.fieldNotation false

variable [lc : LevelClass]

theorem soundness {Γ} {a A : Term} (h : Γ ⊢ a ∶ A) : Γ ⊨ a ∶ A := by
  induction h using wtInd <;> intro σ hσ
  case var mem => exact hσ _ _ mem
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
    let ⟨j, rj, ltj⟩ := hj
    exact ⟨ℓ, _,
      interpsBwds (pars𝒰 rk) (interps𝒰 ltk),
      ⟨_, interpsBwds (pars𝒰 rj) (interps𝒰 ltj)⟩⟩
  case mty ih =>
    let ⟨_, _, hj, hi⟩ := ih σ hσ
    let ⟨j, _, _, e⟩ := interps𝒰Inv hj; subst e
    let ⟨P, hi⟩ := hi
    let ⟨_, _, _, e⟩ := interps𝒰Inv hi; subst e
    exact ⟨j, _, hi, ⟨_, interpsMty⟩⟩
  case exf ihb =>
    let ⟨_, _, hmty, hb⟩ := ihb σ hσ
    rw [interpsMtyInv hmty] at hb
    contradiction
  case lvl iha ihj =>
    let ⟨_, _, hj, hi⟩ := ihj σ hσ
    let ⟨j, _, _, e⟩ := interps𝒰Inv hj; subst e
    let ⟨P, hi⟩ := hi
    let ⟨_, _, _, e⟩ := interps𝒰Inv hi; subst e
    let ⟨_, P, hlvl, ha⟩ := iha σ hσ
    let ⟨_, _, e⟩ := interpsLvlInv hlvl; subst e
    let ⟨k, r, _⟩ := ha
    refine ⟨_, _, hi, ⟨_, interpsBwds (parsLvl r) interpsLvl⟩⟩
  case lof j k _ lt =>
    exact ⟨j, _, interpsLvl, ⟨_, Pars.refl _, lt⟩⟩
  case trans j k _ _ ihj ihk =>
    let ⟨k, Pj, hk, hj⟩ := ihk σ hσ
    let ⟨k, _, ePj⟩ := interpsLvlInv hk
    subst ePj
    let ⟨j, rj, _⟩ := hj
    let ⟨_, Pi, hj, hi⟩ := ihj σ hσ
    let ⟨j', rj', ePi⟩ := interpsLvlInv hj
    subst ePi
    let ⟨i, r, _⟩ := hi
    let ⟨j'', rj, rj'⟩ := confluence rj rj'
    rw [parsLofInv rj] at rj'
    injection (parsLofInv rj') with e; subst e
    refine ⟨_, _, hk, ⟨i, r, ?_⟩⟩
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
    let ⟨_, rj', ltj'⟩ := hj
    let ⟨_, rj, rj'⟩ := confluence rj rj'
    rw [parsLofInv rj'] at rj
    injection (parsLofInv rj) with e; subst e
    let ⟨_, ltk⟩ := exists_gt k
    exact ⟨_, _,
      interpsBwds (pars𝒰 rk) (interps𝒰 ltk),
      ⟨_, interpsCumul ltj' hA⟩⟩

/-*-----------------------------------------
  Canonicity corollaries for closed terms:
  * Empty type is uninhabited
  * Universes contain types
  * Level terms are internalized levels
-----------------------------------------*-/

theorem consistency {b} : ¬ ⬝ ⊢ b ∶ mty := by
  intro h
  let ⟨_, _, hmty, hb⟩ := soundness h var (semSubstNil _)
  simp [interpsMtyInv hmty] at hb

theorem canon𝒰 {T j} (h : ⬝ ⊢ T ∶ 𝒰 j) :
  (∃ A B, T ⇒⋆ pi A B) ∨
  (∃ i, T ⇒⋆ 𝒰 i) ∨
  (T ⇒⋆ mty) ∨
  (∃ k, T ⇒⋆ lvl (lof k)) := by
  let ⟨_, _, h𝒰, hT⟩ := soundness h var (semSubstNil _)
  let ⟨_, _, _, e⟩ := interps𝒰Inv h𝒰; subst e
  let ⟨_, hT⟩ := hT; rw [substId] at hT
  exact interpsStepInv hT

theorem canonLvl {a k} (h : ⬝ ⊢ a ∶ lvl k) : ∃ j, a ⇒⋆ lof j := by
  let ⟨_, _, hlvl, ha⟩ := soundness h var (semSubstNil _)
  let ⟨_, _, e⟩ := interpsLvlInv hlvl; subst e
  let ⟨_, r, _⟩ := ha; rw [substId] at *
  exact ⟨_, r⟩
