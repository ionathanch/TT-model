import «TT-model».syntactics
import «TT-model».reduction
import «TT-model».typing
import «TT-model».semantics

open Term

set_option autoImplicit false
set_option pp.fieldNotation false

variable [lc : LevelClass]

theorem soundness {Γ} {a A : Term} (h : Γ ⊢ a ∶ A) : Γ ⊨ a ∶ A := by
  generalize e : @Sigma.mk I idx I.wt ⟨Γ, a, A⟩ = t at h
  induction h generalizing Γ a A
  all_goals injection e with eI e; injection eI
  all_goals injection e with eCtxt eTerm eType;
            subst eCtxt; subst eTerm; subst eType
  all_goals intro σ hσ
  case var mem => apply hσ; assumption
  case pi ihA ihB =>
    let ⟨i, P, h𝒰, hA⟩ := ihA rfl σ hσ
    let ⟨_, _, ra, e⟩ := interps𝒰Inv h𝒰
    exists i, P; subst e
    let ⟨PA, hA⟩ := hA
    constructor
    . assumption
    . constructor; apply interpsPi hA _ rfl
      intro x PAx; rw [← substUnion]
      let ⟨_, _, h𝒰, hB⟩ := ihB rfl (x +: σ) (semSubstCons hA PAx hσ)
      let ⟨_, _, rb, e⟩ := interps𝒰Inv h𝒰
      subst e; rw [substRename] at rb
      let ⟨_, ra', rb'⟩ := confluence ra rb
      rw [parsLofInv ra'] at rb'
      injection (parsLofInv rb') with e
      simp_rw [e, hB]
  case abs ihpi ihb =>
    let ⟨_, _, h𝒰, hpi⟩ := ihpi rfl σ hσ
    let ⟨_, _, _, e⟩ := interps𝒰Inv h𝒰
    subst e
    let ⟨P, hpi⟩ := hpi
    let ⟨Pa, hA, _, e⟩ := interpsPiInv hpi
    constructor; exists P; constructor
    . exact hpi
    . subst e; intro x Pb PAx hB; rw [← substUnion] at hB
      let ⟨_, _, hB', hb⟩ := ihb rfl (x +: σ) (semSubstCons hA PAx hσ)
      rw [interpsDet hB hB']
      exact interpsBwdsP (parsβ σ) hB' hb
  case app ihb iha =>
    let ⟨i, _, hpi, hb⟩ := ihb rfl σ hσ
    let ⟨_, PA, hA, ha⟩ := iha rfl σ hσ
    let ⟨PA', hA', hB, e⟩ := interpsPiInv hpi
    rw [interpsDet hA hA'] at ha
    let ⟨PB, hB⟩ := hB (subst σ _) ha
    subst e; rw [← substDist]
    exists i, PB; constructor <;> apply_rules
  case 𝒰 ih =>
    let ⟨_, P, hk, hj⟩ := ih rfl σ hσ
    let ⟨k, rk, e⟩ := interpsLvlInv hk
    subst e
    let ⟨j, rj, ltj⟩ := hj
    let ⟨ℓ, ltk⟩ := exists_gt k
    exists ℓ, (∃ P, ⟦ · ⟧ k ↘ P); constructor
    . exact interpsBwds (pars𝒰 rk) (interps𝒰 ltk)
    . constructor; exact interpsBwds (pars𝒰 rj) (interps𝒰 ltj)
  case mty ih =>
    let ⟨_, _, hj, hi⟩ := ih rfl σ hσ
    let ⟨j, _, e⟩ := interpsLvlInv hj
    subst e
    let ⟨i, ri, lt⟩ := hi
    refine ⟨j, (∃ P, ⟦ · ⟧ i ↘ P), ?_, ?_⟩
    . exact interpsBwds (pars𝒰 ri) (interps𝒰 lt)
    . constructor; exact interpsMty
  case exf ihb _ _ =>
    let ⟨_, _, hmty, hb⟩ := ihb rfl σ hσ
    rw [interpsMtyInv hmty] at hb
    contradiction
  case lvl k _ iha =>
    let ⟨_, P, hlvl, ha⟩ := iha rfl σ hσ
    let ⟨ℓ, lt⟩ := exists_gt k
    refine ⟨ℓ, (∃ P, ⟦ · ⟧ k ↘ P), interps𝒰 lt, ?_⟩
    let ⟨_, _, e⟩ := interpsLvlInv hlvl
    subst e
    let ⟨k, r, _⟩ := ha
    exists (∃ j, · ⇒⋆ lof j ∧ j < k)
    exact interpsBwds (parsLvl r) interpsLvl
  case lof j k _ _ _ =>
    refine ⟨j, (∃ j, · ⇒⋆ lof j ∧ j < k), interpsLvl, ?_⟩
    exists j, Pars.refl _
  case trans j k _ ihk _ ihj =>
    let ⟨k, Pj, hk, hj⟩ := ihk rfl σ hσ
    let ⟨k, _, ePj⟩ := interpsLvlInv hk
    subst ePj
    let ⟨j, rj, _⟩ := hj
    let ⟨_, Pi, hj, hi⟩ := ihj rfl σ hσ
    let ⟨j', rj', ePi⟩ := interpsLvlInv hj
    subst ePi
    let ⟨i, r, _⟩ := hi
    let ⟨j'', rj, rj'⟩ := confluence rj rj'
    rw [parsLofInv rj] at rj'
    injection (parsLofInv rj') with e; subst e
    refine ⟨_, (∃ j, · ⇒⋆ lof j ∧ j < k), hk, ?_⟩
    exists i, r; apply IsTrans.trans <;> assumption
  case conv iha conv _ _ =>
    let ⟨i, P, hA, ha⟩ := iha rfl σ hσ
    exists i, P; constructor
    . exact interpsConv (convSubst σ (eqvConv conv)) hA
    . exact ha
  case sub ihj _ ihA =>
    let ⟨_, Pj, h𝒰, hA⟩ := ihA rfl σ hσ
    let ⟨j, _, rj, e⟩ := interps𝒰Inv h𝒰
    subst e
    let ⟨P, hA⟩ := hA
    let ⟨_, Pk, hk, hj⟩ := ihj rfl σ hσ
    let ⟨k, rk, e⟩ := interpsLvlInv hk
    subst e
    let ⟨j', rj', ltj'⟩ := hj
    let ⟨j'', rj, rj'⟩ := confluence rj rj'
    rw [parsLofInv rj'] at rj
    injection (parsLofInv rj) with e; subst e
    let ⟨ℓ, ltk⟩ := exists_gt k
    refine ⟨ℓ, (∃ P, ⟦ · ⟧ k ↘ P), ?_, ?_⟩
    . exact interpsBwds (pars𝒰 rk) (interps𝒰 ltk)
    . exists P; exact interpsCumul ltj' hA

theorem consistency {b} : ¬ ⬝ ⊢ b ∶ mty := by
  intro h
  let ⟨_, _, hmty, hb⟩ := soundness h var (semSubstNil _)
  simp [interpsMtyInv hmty] at hb
