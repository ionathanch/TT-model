import «TT-model».syntactics
import «TT-model».reduction
import «TT-model».typing
import «TT-model».semantics

open Nat
open Term
open Ctxt (nil)

set_option autoImplicit false

theorem soundness {Γ a A} : (Γ ⊢ a ⦂ A) → (Γ ⊨ a ⦂ A)
  | Wt.var wf mem => by intro σ hσ; apply hσ <;> assumption
  | Wt.pi thA thB => by
    intro σ hσ
    match soundness thA σ hσ with
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
      match soundness thB (x +: σ) (semSubstCons hA PAx hσ) with
      | ⟨_, _, h𝒰, hB⟩ =>
      match interps𝒰Inv h𝒰 with
      | ⟨_, e⟩ => subst e; exact hB
  | Wt.abs thpi thb => by
    intro σ hσ
    match soundness thpi σ hσ with
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
      match soundness thb (x +: σ) (semSubstCons hA PAx hσ) with
      | ⟨_, _, hB', hb⟩ =>
      rw [interpsDet hB hB']
      apply interpsBwdsP _ hB' hb
      apply parsβ
  | Wt.app thb tha => by
    intro σ hσ
    match soundness thb σ hσ with
    | ⟨i, _, hpi, hb⟩ =>
    match soundness tha σ hσ with
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
  | @Wt.𝒰 _ _ j _ lt => by
    intro σ hσ
    exists (succ j), (∃ P, ⟦ · ⟧ j ↘ P); constructor
    . apply interps𝒰; omega
    . constructor; apply interps𝒰 lt
  | @Wt.mty _ i _ => by
    intro σ hσ
    exists (succ i), (∃ P, ⟦ · ⟧ i ↘ P); constructor
    . apply interps𝒰; omega
    . constructor; apply interpsMty
  | Wt.exf _ thb => by
    intro σ hσ
    match soundness thb σ hσ with
    | ⟨_, _, hmty, hb⟩ =>
    rw [interpsMtyInv hmty] at hb
    contradiction
  | Wt.conv conv tha thB => by
    intro σ hσ
    match soundness tha σ hσ with
    | ⟨i, P, hA, ha⟩ =>
    exists i, P; constructor
    . apply interpsConv _ hA; apply convSubst σ; apply eqvConv conv
    . exact ha
termination_by sizeOf Wt
decreasing_by repeat sorry
-- FIXME: temporary measure as Lean doesn't support `induction` on mutual inductives
-- or structural recursion on inductive predicates...

theorem consistency {b} : ¬ (nil ⊢ b ⦂ mty) := by
  intro h; match soundness h var (semSubstNil _) with
  | ⟨_, _, hmty, hb⟩ => rw [interpsMtyInv hmty] at hb; exact hb
