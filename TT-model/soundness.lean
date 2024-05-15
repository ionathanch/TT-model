import «TT-model».syntactics
import «TT-model».reduction
import «TT-model».typing
import «TT-model».semantics

open Nat
open Term
open Ctxt (nil)

set_option autoImplicit false

theorem soundness {Γ a A} (h : Γ ⊢ a ⦂ A) : (Γ ⊨ a ⦂ A) := by
  generalize e : @Sigma.mk I idx I.wt (T.mk Γ a A) = t at h
  revert Γ a A e; induction h
  all_goals intro Γ a A e; injection e with eI e; injection eI
  all_goals injection e with eCtxt eTerm eType;
            subst eCtxt; subst eTerm; subst eType
  all_goals intro σ hσ
  case var mem => apply hσ <;> assumption
  case pi ihA ihB =>
    match ihA rfl σ hσ with
    | ⟨i, P, h𝒰, hA⟩ =>
    match interps𝒰Inv h𝒰 with
    | ⟨_, e⟩ =>
    exists i, P; subst e
    match hA with
    | ⟨PA, hA⟩ =>
    constructor
    . assumption
    . constructor; apply interpsPi hA _ rfl
      intro x PAx; rw [← substUnion]
      match ihB rfl (x +: σ) (semSubstCons hA PAx hσ) with
      | ⟨_, _, h𝒰, hB⟩ =>
      match interps𝒰Inv h𝒰 with
      | ⟨_, e⟩ => subst e; exact hB
  case abs ihpi ihb =>
    match ihpi rfl σ hσ with
    | ⟨_, _, h𝒰, hpi⟩ =>
    match interps𝒰Inv h𝒰 with
    | ⟨_, e⟩ =>
    subst e
    match hpi with
    | ⟨P, hpi⟩ =>
    match interpsPiInv hpi with
    | ⟨Pa, hA, _, e⟩ =>
    constructor; exists P; constructor
    . exact hpi
    . subst e; intro x Pb PAx hB; rw [← substUnion] at hB
      match ihb rfl (x +: σ) (semSubstCons hA PAx hσ) with
      | ⟨_, _, hB', hb⟩ =>
      rw [interpsDet hB hB']
      apply interpsBwdsP _ hB' hb
      apply parsβ
  case app ihb iha =>
    match ihb rfl σ hσ with
    | ⟨i, _, hpi, hb⟩ =>
    match iha rfl σ hσ with
    | ⟨_, PA, hA, ha⟩ =>
    match interpsPiInv hpi with
    | ⟨PA', hA', hB, e⟩ =>
    rw [interpsDet hA hA'] at ha
    match hB (subst σ _) ha with
    | ⟨PB, hB⟩ =>
    subst e; rw [← substDist]
    exists i, PB; constructor
    . exact hB
    . apply hb <;> assumption
  case 𝒰 j lt _ _ =>
    exists (succ j), (∃ P, ⟦ · ⟧ j ↘ P); constructor
    . simp; apply interps𝒰; omega
    . constructor; apply interps𝒰 lt
  case mty i _ _ =>
    exists (succ i), (∃ P, ⟦ · ⟧ i ↘ P); constructor
    . apply interps𝒰; omega
    . constructor; apply interpsMty
  case exf ihb _ _ =>
    match ihb rfl σ hσ with
    | ⟨_, _, hmty, hb⟩ =>
    rw [interpsMtyInv hmty] at hb
    contradiction
  case conv iha conv _ _ =>
    match iha rfl σ hσ with
    | ⟨i, P, hA, ha⟩ =>
    exists i, P; constructor
    . apply interpsConv _ hA; apply convSubst σ; apply eqvConv conv
    . exact ha

theorem consistency {b} : ¬ (nil ⊢ b ⦂ mty) := by
  intro h; match soundness h var (semSubstNil _) with
  | ⟨_, _, hmty, hb⟩ => rw [interpsMtyInv hmty] at hb; exact hb
