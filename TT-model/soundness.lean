import «TT-model».syntactics
import «TT-model».reduction
import «TT-model».typing
import «TT-model».semantics

open LevelClass (lsucc)
open Term

set_option autoImplicit false

variable [lc : LevelClass]

theorem soundness {Γ a A} (h : Γ ⊢ a ∶ A) : Γ ⊨ a ∶ A := by
  generalize e : @Sigma.mk I idx I.wt ⟨Γ, a, A⟩ = t at h
  revert Γ a A e; induction h
  all_goals intro Γ a A e; injection e with eI e; injection eI
  all_goals injection e with eCtxt eTerm eType;
            subst eCtxt; subst eTerm; subst eType
  all_goals intro σ hσ
  case var mem => apply hσ; assumption
  case pi ihA ihB =>
    match ihA rfl σ hσ with
    | ⟨i, P, h𝒰, hA⟩ =>
    match interps𝒰Inv h𝒰 with
    | ⟨_, ra, _, e⟩ =>
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
      | ⟨_, rb, _, e⟩ =>
      subst e; rw [substRenamed] at rb
      match confluence ra rb with
      | ⟨_, ra', rb'⟩ =>
      rw [parsLofInv ra'] at rb';
      injection (parsLofInv rb') with e;
      simp [e, hB]
  case abs ihpi ihb =>
    match ihpi rfl σ hσ with
    | ⟨_, _, h𝒰, hpi⟩ =>
    match interps𝒰Inv h𝒰 with
    | ⟨_, _, _, e⟩ =>
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
  case 𝒰 ih =>
    match ih rfl σ hσ with
    | ⟨_, P, hk, hj⟩ =>
    match interpsLvlInv hk with
    | ⟨k, rk, e⟩ =>
    subst e
    match hj with
    | ⟨j, rj, ltj⟩ =>
    match lsucc k with
    | ⟨ℓ, ltk⟩ =>
    exists ℓ, (∃ P, ⟦ · ⟧ k ↘ P); constructor
    . simp; exact interpsBwds (pars𝒰 rk) (interps𝒰 ltk)
    . constructor; exact interpsBwds (pars𝒰 rj) (interps𝒰 ltj)
  case mty ih =>
    match ih rfl σ hσ with
    | ⟨_, _, hj, hi⟩ =>
    match interpsLvlInv hj with
    | ⟨j, _, e⟩ =>
    subst e
    match hi with
    | ⟨i, ri, lt⟩ =>
    refine ⟨j, (∃ P, ⟦ · ⟧ i ↘ P), ?_, ?_⟩
    . exact interpsBwds (pars𝒰 ri) (interps𝒰 lt)
    . constructor; exact interpsMty
  case exf ihb _ _ =>
    match ihb rfl σ hσ with
    | ⟨_, _, hmty, hb⟩ =>
    rw [interpsMtyInv hmty] at hb
    contradiction
  case lvl k _ iha =>
    match iha rfl σ hσ with
    | ⟨_, P, hlvl, ha⟩ =>
    match lsucc k with
    | ⟨ℓ, lt⟩ =>
    refine ⟨ℓ, (∃ P, ⟦ · ⟧ k ↘ P), ?_, ?_⟩
    . apply interps𝒰 lt
    . match interpsLvlInv hlvl with
      | ⟨_, _, e⟩ =>
      subst e
      match ha with
      | ⟨k, r, _⟩ =>
      exists (∃ j, · ⇒⋆ lof j ∧ j < k)
      exact interpsBwds (parsLvl r) interpsLvl
  case lof j k _ _ _ =>
    refine ⟨j, (∃ j, · ⇒⋆ lof j ∧ j < k), ?_, ?_⟩
    . exact interpsLvl
    . exists j, Pars.refl _
  case trans j k _ ihk _ ihj =>
    match ihk rfl σ hσ with
    | ⟨k, Pj, hk, hj⟩ =>
    match interpsLvlInv hk with
    | ⟨k, _, ePj⟩ =>
    subst ePj
    match hj with
    | ⟨j, rj, _⟩ =>
    match ihj rfl σ hσ with
    | ⟨_, Pi, hj, hi⟩ =>
    match interpsLvlInv hj with
    | ⟨j', rj', ePi⟩ =>
    subst ePi
    match hi with
    | ⟨i, r, _⟩ =>
    match confluence rj rj' with
    | ⟨j'', rj, rj'⟩ =>
    rw [parsLofInv rj] at rj'
    injection (parsLofInv rj') with e; subst e
    refine ⟨_, (∃ j, · ⇒⋆ lof j ∧ j < k), hk, ?_⟩
    . exists i, r; apply IsTrans.trans <;> assumption
  case conv iha conv _ _ =>
    match iha rfl σ hσ with
    | ⟨i, P, hA, ha⟩ =>
    exists i, P; constructor
    . exact interpsConv (convSubst σ (eqvConv conv)) hA
    . exact ha
  case sub ihj _ ihA =>
    match ihA rfl σ hσ with
    | ⟨_, Pj, h𝒰, hA⟩ =>
    match interps𝒰Inv h𝒰 with
    | ⟨j, rj, _ , e⟩ =>
    subst e
    match hA with
    | ⟨P, hA⟩ =>
    match ihj rfl σ hσ with
    | ⟨_, Pk, hk, hj⟩ =>
    match interpsLvlInv hk with
    | ⟨k, rk, e⟩ =>
    subst e
    match hj with
    | ⟨j', rj', ltj'⟩ =>
    match confluence rj rj' with
    | ⟨j'', rj, rj'⟩ =>
    rw [parsLofInv rj'] at rj
    injection (parsLofInv rj) with e; subst e
    match lsucc k with
    | ⟨ℓ, ltk⟩ =>
    refine ⟨ℓ, (∃ P, ⟦ · ⟧ k ↘ P), ?_, ?_⟩
    . exact interpsBwds (pars𝒰 rk) (interps𝒰 ltk)
    . exists P; exact interpsCumul ltj' hA

theorem consistency {b} : ¬ ⬝ ⊢ b ∶ mty := by
  intro h; match soundness h var (semSubstNil _) with
  | ⟨_, _, hmty, hb⟩ => rw [interpsMtyInv hmty] at hb; exact hb
