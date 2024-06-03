import «TT-model».syntactics
import «TT-model».reduction
import «TT-model».typing
import «TT-model».semantics

open Term
open LevelClass

set_option autoImplicit false
set_option pp.fieldNotation false

variable [LevelClass]

theorem soundness {idx} (h : Wtf idx) :
  match idx with
  | ⟨I.wt𝒰, ⟨Γ, a, A⟩⟩ => Γ ⊨ a ∶ A
  | ⟨I.wtℙ, ⟨Γ, a, A⟩⟩ => Γ ⊨ₚ a ∶ A
  | ⟨I.wf, _⟩ => True
  := by
  induction h
  all_goals simp
  all_goals intro σ hσ
  case var x A _ mem _ => let ⟨in𝒰, _⟩ := hσ x A; exact in𝒰 mem
  case ivar x A _ mem _ => let ⟨_, inℙ⟩ := hσ x A; exact inℙ mem
  case 𝒰 j k ltj =>
    let ⟨ℓ, ltk⟩ := exists_gt k
    exact ⟨ℓ, _, interps𝒰 ltk, ⟨_, interps𝒰 ltj⟩⟩
  case pi ihA ihB =>
    simp [*] at *
    let ⟨i, P, h𝒰, hA⟩ := ihA σ hσ
    let ⟨_, e⟩ := interps𝒰Inv h𝒰
    exists i, P; subst e
    let ⟨PA, hA⟩ := hA
    constructor
    . assumption
    . constructor; apply interpsPi hA _ rfl
      intro x PAx
      change ∃ Pb, ⟦ subst (x +: var) (subst (⇑ σ) _) ⟧ _ ↘ Pb
      rw [← substUnion]
      let ⟨_, _, h𝒰, hB⟩ := ihB (x +: σ) (semSubstCons hA PAx hσ)
      let ⟨_, e⟩ := interps𝒰Inv h𝒰
      subst e; exact hB
  case abs ihpi ihb =>
    let ⟨_, _, h𝒰, hpi⟩ := ihpi σ hσ
    let ⟨_, e⟩ := interps𝒰Inv h𝒰
    subst e
    let ⟨P, hpi⟩ := hpi
    let ⟨Pa, hA, _, e⟩ := interpsPiInv hpi
    constructor; exists P; constructor
    . exact hpi
    . subst e; intro x Pb PAx hB; rw [← substUnion] at hB
      let ⟨_, _, hB', hb⟩ := ihb (x +: σ) (semSubstCons hA PAx hσ)
      rw [interpsDet hB hB']
      exact interpsBwdsP (parsβ _ _ _) hB' hb
  case app ihb iha =>
    let ⟨i, _, hpi, hb⟩ := ihb σ hσ
    let ⟨_, PA, hA, ha⟩ := iha σ hσ
    let ⟨PA', hA', hB, e⟩ := interpsPiInv hpi
    rw [interpsDet hA hA'] at ha
    let ⟨PB, hB⟩ := hB (subst σ _) ha
    subst e; rw [← substDist]
    exists i, PB; constructor <;> apply_rules
  case ℙ =>
    let ⟨«1», lt⟩ := exists_gt «0»
    exists «1», (∃ P, ⟦ · ⟧ «0» ↘ P); constructor
    . exact interps𝒰 lt
    . constructor; exact interpsℙ
  case all =>
    exists «0», (∃ P, IInterp · P), interpsℙ
    exists λ _ ↦ True, λ _ _ ↦ True; simp
  case iabs ihA ihb =>
    let ⟨_, _, h𝒰, hA⟩ := ihA σ hσ
    let ⟨_, e⟩ := interps𝒰Inv h𝒰
    subst e
    let ⟨PA, hA⟩ := hA
    constructor; constructor
    . apply interpsAll hA ?_ rfl
      intro x PAx
      let ⟨PB, hB, _⟩ := ihb (x +: σ) (semSubstCons hA PAx hσ)
      rw [substUnion] at hB; exists PB
    . intro x PB PAx hB
      let ⟨PB', hB', hb⟩ := ihb (x +: σ) (semSubstCons hA PAx hσ)
      rw [← substUnion] at hB
      rw [interpDet₀ hB hB']
      exact interpBwdsP₀ (parsβ _ _ _) hB' hb
  case iapp A _ _ _ _ _ ihb iha =>
    let ⟨_, hall, hb⟩ := ihb σ hσ
    let ⟨_, PA, hA, ha⟩ := iha σ hσ
    let ⟨_, PA', hA', hB, e⟩ := interpAllInv hall
    rw [interpsDet hA hA'] at ha
    let ⟨PB, hB⟩ := hB (subst σ _) ha
    subst e; rw [← substDist]
    exists PB; constructor <;> apply_rules
  case mty =>
    refine ⟨«0», _, interpsℙ, ?_⟩
    exists λ _ ↦ True, λ _ _ ↦ True; simp
  case exf ihb =>
    let ⟨_, hmty, hb⟩ := ihb σ hσ
    rw [interpMtyInv hmty] at hb
    contradiction
  case iexf ihb =>
    let ⟨_, hmty, hb⟩ := ihb σ hσ
    rw [interpMtyInv hmty] at hb
    contradiction
  case conv conv _ _ iha _ =>
    let ⟨i, P, hA, ha⟩ := iha σ hσ
    exact ⟨i, P, interpsConv (convSubst σ (eqvConv conv)) hA, ha⟩
  case iconv conv _ _ iha _ =>
    let ⟨P, hA, ha⟩ := iha σ hσ
    exact ⟨P, interpConv₀ (convSubst σ (eqvConv conv)) hA, ha⟩
  case sub j k _ ltj _ ihA =>
    let ⟨_, Pj, h𝒰, hA⟩ := ihA σ hσ
    let ⟨_, e⟩ := interps𝒰Inv h𝒰
    subst e
    let ⟨P, hA⟩ := hA
    let ⟨ℓ, ltk⟩ := exists_gt k
    exact ⟨ℓ, _, interps𝒰 ltk, ⟨P, interpsCumul ltj hA⟩⟩
  case isub k _ ihA =>
    let ⟨_, _, hℙ, hA⟩ := ihA σ hσ
    rw [interpsℙInv hℙ] at hA
    let ⟨P, hA⟩ := hA
    let ⟨ℓ, ltk⟩ := exists_gt k
    refine ⟨ℓ, _, interps𝒰 ltk, ⟨P, ?_⟩⟩
    sorry

theorem consistency {b} : ¬ ⬝ ⊢ₚ b ∶ mty := by
  intro h
  let ⟨_, hmty, hb⟩ := soundness h var (semSubstNil var)
  simp [interpMtyInv hmty] at hb
