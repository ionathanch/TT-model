import «TT-model».syntactics
import «TT-model».reduction
import «TT-model».typing

open Nat
open Term

set_option autoImplicit false
set_option pp.fieldNotation false

variable [LevelClass]

/-*----------------------
  Well-scoped renamings
----------------------*-/

def wRename ξ Γ Δ := ∀ x A, Γ ∋ x ∶ A → Δ ∋ ξ x ∶ rename ξ A
notation:40 Δ:41 "⊢" ξ:41 "∶" Γ:41 => wRename ξ Γ Δ

theorem wRenameLift {ξ : ℕ → ℕ} {Γ Δ A}
  (h : Δ ⊢ ξ ∶ Γ) :
  Δ ∷ (rename ξ A) ⊢ lift ξ ∶ Γ ∷ A := by
  intro x B mem
  cases mem with
  | here => apply inHere; simp [renameComp]; rfl
  | there => apply inThere; apply_rules [h]; simp [h, renameComp]; rfl

theorem wRenameSucc {Γ A} : Γ ∷ A ⊢ succ ∶ Γ := by
  intro x B mem; constructor; assumption

/-*------------------------------
  Renaming and weakening lemmas
------------------------------*-/

theorem wtRename {ξ : ℕ → ℕ} {Γ Δ} {a A : Term}
  (hξ : Δ ⊢ ξ ∶ Γ) (hΔ : ⊢ Δ) (h : Γ ⊢ a ∶ A) :
  Δ ⊢ rename ξ a ∶ rename ξ A := by
  generalize e : @Sigma.mk I idx I.wt ⟨Γ, a, A⟩ = t at h
  induction h generalizing ξ Γ Δ a A
  all_goals injection e with eI e; injection eI
  all_goals injection e with eCtxt eTerm eType;
            subst eCtxt; subst eTerm; subst eType
  case var => constructor; assumption; apply_rules [hξ]
  case 𝒰 ih => exact Wtf.𝒰 (ih hξ hΔ rfl)
  case pi ihA ihB =>
    let ihA' := ihA hξ hΔ rfl
    refine Wtf.pi ihA' ?_
    rw [renameLiftRename]
    exact ihB (wRenameLift hξ) (Wtf.cons hΔ ihA') rfl
  case abs ihPi ihb =>
    let ihPi' := ihPi hξ hΔ rfl
    refine Wtf.abs ihPi' ?_
    let ⟨k, hA⟩ := wtfPiInvA ihPi'
    exact ihb (wRenameLift hξ) (Wtf.cons hΔ hA) rfl
  case app ihb iha => rw [← renameDist]; exact Wtf.app (ihb hξ hΔ rfl) (iha hξ hΔ rfl)
  case mty ih => exact Wtf.mty (ih hξ hΔ rfl)
  case exf ihA _ ihb => exact Wtf.exf (ihb hξ hΔ rfl) (ihA hξ hΔ rfl)
  case lvl ih => exact Wtf.lvl (ih hξ hΔ rfl)
  case lof => constructor <;> assumption
  case trans ihi _ ihj => exact Wtf.trans (ihj hξ hΔ rfl) (ihi hξ hΔ rfl)
  case conv B _ _ iha h _ ihA =>
    exact Wtf.conv (convEqv (convRename ξ (eqvConv h))) (iha hξ hΔ rfl) (ihA hξ hΔ rfl)
  case sub ihj _ ihA => exact Wtf.sub (ihj hξ hΔ rfl) (ihA hξ hΔ rfl)

theorem wtWeaken {Γ k} {a A B : Term}
  (hΓ : ⊢ Γ) (hB : Γ ⊢ B ∶ 𝒰 k) (h : Γ ⊢ a ∶ A) :
  Γ ∷ B ⊢ rename succ a ∶ rename succ A := by
  apply wtRename wRenameSucc (Wtf.cons hΓ hB) h

/-*-------------------------
  Well-typed substitutions
-------------------------*-/

def wSubst σ Γ Δ := ∀ x A, Γ ∋ x ∶ A → Δ ⊢ σ x ∶ subst σ A
notation:40 Δ:41 "⊢" σ:41 "∶" Γ:41 => wSubst σ Γ Δ

theorem wSubstUp {σ Δ Γ k A}
  (hA : Δ ⊢ subst σ A ∶ 𝒰 k)
  (h : Δ ⊢ σ ∶ Γ) :
  Δ ∷ subst σ A ⊢ ⇑ σ ∶ Γ ∷ A := by
  intro x B mem; cases mem
  all_goals rw [← renameUpSubst]
  . exact Wtf.var (Wtf.cons (wtWf hA) hA) In.here
  . refine wtWeaken (wtWf hA) hA (h _ _ ?_); assumption

theorem wSubstCons {Γ} {a A : Term}
  (h : Γ ⊢ a ∶ A) :
  Γ ⊢ a +: var ∶ Γ ∷ A := by
  intro x B mem; cases mem
  all_goals rw [← substDrop]
  . exact h
  . refine Wtf.var (wtWf h) ?_; assumption

/-*---------------------------------
  Morphing and substitution lemmas
---------------------------------*-/

theorem wtMorph {σ : ℕ → Term} {Γ Δ} {a A : Term}
  (hσ : Δ ⊢ σ ∶ Γ) (hΔ : ⊢ Δ) (h : Γ ⊢ a ∶ A) :
  Δ ⊢ subst σ a ∶ subst σ A := by
  generalize e : @Sigma.mk I idx I.wt ⟨Γ, a, A⟩ = t at h
  induction h generalizing σ Γ Δ a A
  all_goals injection e with eI e; injection eI
  all_goals injection e with eCtxt eTerm eType;
            subst eCtxt; subst eTerm; subst eType
  case var mem => exact hσ _ _ mem
  case 𝒰 ih => exact Wtf.𝒰 (ih hσ hΔ rfl)
  case pi ihA ihB =>
    let ihA' := ihA hσ hΔ rfl
    refine Wtf.pi ihA' ?_
    rw [renameUpSubst]
    exact ihB (wSubstUp ihA' hσ) (Wtf.cons hΔ ihA') rfl
  case abs ihPi ihb =>
    let ihPi' := ihPi hσ hΔ rfl
    refine Wtf.abs ihPi' ?_
    let ⟨k, hA⟩ := wtfPiInvA ihPi'
    exact ihb (wSubstUp hA hσ) (Wtf.cons hΔ hA) rfl
  case app ihb iha => rw [← substDist]; exact Wtf.app (ihb hσ hΔ rfl) (iha hσ hΔ rfl)
  case mty ih => exact Wtf.mty (ih hσ hΔ rfl)
  case exf ihA _ ihb => exact Wtf.exf (ihb hσ hΔ rfl) (ihA hσ hΔ rfl)
  case lvl ih => exact Wtf.lvl (ih hσ hΔ rfl)
  case lof => constructor <;> assumption
  case trans ihi _ ihj => exact Wtf.trans (ihj hσ hΔ rfl) (ihi hσ hΔ rfl)
  case conv B _ _ iha h _ ihA =>
    refine Wtf.conv (convEqv (convSubst σ (eqvConv h))) (iha hσ hΔ rfl) (ihA hσ hΔ rfl)
  case sub ihj _ ihA => exact Wtf.sub (ihj hσ hΔ rfl) (ihA hσ hΔ rfl)

theorem wtSubst {Γ} {a A b B : Term}
  (hb : Γ ⊢ b ∶ B) (h : Γ ∷ B ⊢ a ∶ A) :
  Γ ⊢ subst (b +: var) a ∶ subst (b +: var) A := by
  apply wtMorph (wSubstCons hb) (wtWf hb) h

/-*-----------
  Regularity
-----------*-/

theorem wtMem {Γ x A} (mem : Γ ∋ x ∶ A) (h : ⊢ Γ) : ∃ k, Γ ⊢ A ∶ 𝒰 k := by
  induction mem
  case here =>
    cases h with
    | cons hΓ hB =>
      exact ⟨rename succ _, wtWeaken hΓ hB hB⟩
  case there ih =>
    cases h with
    | cons hΓ hB =>
      let ⟨k, hA⟩ := ih hΓ
      exact ⟨rename succ k, wtWeaken hΓ hB hA⟩

theorem wtRegularity {Γ} {a A : Term} (h : Γ ⊢ a ∶ A) : ∃ k, Γ ⊢ A ∶ 𝒰 k := by
  generalize e : @Sigma.mk I idx I.wt ⟨Γ, a, A⟩ = t at h
  induction h generalizing Γ a A
  all_goals injection e with eI e; injection eI
  all_goals injection e with eCtxt eTerm eType;
            subst eCtxt; subst eTerm; subst eType
  case var wf _ mem => exact wtMem mem wf
  case 𝒰 j k _ ih =>
    let ⟨_, ihk⟩ := ih rfl
    let ⟨l, hk⟩ := wtfLvlInv ihk
    exact ⟨l, Wtf.𝒰 hk⟩
  case pi ihA _ => exact ihA rfl
  case abs hPi _ _ _ => exact ⟨_, hPi⟩
  case app ha ihb _ =>
    let ⟨_, hPi⟩ := ihb rfl
    let ⟨k, hB⟩ := wtfPiInvB hPi
    exact ⟨subst _ k, wtSubst ha hB⟩
  case mty hj _ => exact ⟨_, Wtf.𝒰 hj⟩
  case exf hA _ => exact ⟨_, hA⟩
  case lvl k ha _ =>
    let ⟨l, klgt⟩ := exists_gt k
    exact ⟨lof l, Wtf.𝒰 (Wtf.lof (wtWf ha) klgt)⟩
  case lof k _ wf _ =>
    let ⟨l, klgt⟩ := exists_gt k
    exact ⟨lof l, Wtf.lvl (Wtf.lof wf klgt)⟩
  case trans ih _ _ => exact ih rfl
  case conv hA _ => exact ⟨_, hA⟩
  case sub ih _ _ =>
    let ⟨_, ihk⟩ := ih rfl
    let ⟨l, hk⟩ := wtfLvlInv ihk
    exact ⟨l, Wtf.𝒰 hk⟩
