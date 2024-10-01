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
  (corollary: replacement)
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

theorem wtReplace {Γ} {A B c C k : Term}
  (e : A ≈ B)
  (hB : Γ ⊢ B ∶ 𝒰 k)
  (h : Γ ∷ A ⊢ c ∶ C) :
  Γ ∷ B ⊢ c ∶ C := by
  cases wtWf h with | cons wfΓ hA =>
  let wfΓB := Wtf.cons wfΓ hB
  rw [← substId c, ← substId C]
  refine wtMorph ?_ wfΓB h
  intro x A mem; rw [substId]; cases mem
  case here =>
    exact Wtf.conv
      (convEqv (convRename succ (convSym (eqvConv e))))
      (Wtf.var wfΓB In.here)
      (wtWeaken wfΓ hB hA)
  case there mem => exact Wtf.var wfΓB (In.there mem)

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
    let ⟨l, _, hk, _⟩ := wtfLvlInv ihk
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
    let ⟨l, _, hk, _⟩ := wtfLvlInv ihk
    exact ⟨l, Wtf.𝒰 hk⟩

/-*-------------
  Preservation
-------------*-/

theorem wtPar {Γ} {a b A : Term} (r : a ⇒ b) (h : Γ ⊢ a ∶ A) : Γ ⊢ b ∶ A := by
  generalize e : @Sigma.mk I idx I.wt ⟨Γ, a, A⟩ = t at h
  induction h generalizing Γ a b A
  all_goals injection e with eI e; injection eI
  all_goals injection e with eCtxt eTerm eType;
            subst eCtxt; subst eTerm; subst eType
  case var => cases r; constructor <;> assumption
  case 𝒰 ih => cases r with | 𝒰 r' => exact Wtf.𝒰 (ih r' rfl)
  case pi ihA ihB =>
    cases r with | pi ra rb =>
    let ihA' := ihA ra rfl
    exact Wtf.pi ihA' (wtReplace (parEqv ra) ihA' (ihB rb rfl))
  case abs hPi _ _ ihb => cases r with | abs r' => exact Wtf.abs hPi (ihb r' rfl)
  case app hb ha ihb iha =>
    cases r
    case β rb ra =>
      let ⟨_, hA⟩ := wtRegularity ha
      let ⟨_, hPi⟩ := wtRegularity hb
      let ⟨_, hB⟩ := wtfPiInvB hPi
      let ⟨A', B', hb', e⟩ := wtfAbsInv (ihb (Par.abs rb) rfl)
      let ⟨eA, eB⟩ := convPiInv (eqvConv e)
      exact Wtf.conv
        (convEqv (convCong (convSym (parConv ra)) eB))
        (wtSubst (iha ra rfl) (wtReplace (convEqv eA) hA hb'))
        (wtSubst ha hB)
    case app rb ra =>
      let ⟨k, hBa⟩ := wtRegularity (Wtf.app hb ha)
      exact Wtf.conv
        (convEqv (convSym (parConv (parCong ra (parRefl _)))))
        (Wtf.app (ihb rb rfl) (iha ra rfl)) hBa
  case mty ih => cases r; exact Wtf.mty (ih (parRefl _) rfl)
  case exf ihb hA _ => cases r with | exf r' => exact Wtf.exf hA (ihb r' rfl)
  case lvl ih => cases r with | lvl r' => exact Wtf.lvl (ih r' rfl)
  case lof => cases r; constructor <;> assumption
  case trans hj _ _ ihi => exact Wtf.trans (ihi r rfl) hj
  case conv iha eqv hB _ => exact Wtf.conv eqv (iha r rfl) hB
  case sub hj _ _ ihA => exact Wtf.sub hj (ihA r rfl)

/-*---------
  Progress
---------*-/

-- This needs to be in Type, not Prop
-- for the large elim in valueType
inductive Value : Term → Type where
  | 𝒰 {k} : Value (𝒰 k)
  | pi {a b} : Value (pi a b)
  | abs {b} : Value (abs b)
  | mty : Value mty
  | lvl {k} : Value (lvl k)
  | lof {k} : Value (lof k)

section
set_option hygiene false
local infix:40 "⇒β" => CBN
local infix:40 "⇒β⋆" => CBNs

inductive CBN : Term → Term → Prop where
  | β {b a} : app (abs b) a ⇒β subst (a +: var) b
  | app {b b' a} : b ⇒β  b' → app b a ⇒β app b' a
  | exf {b b'} : b ⇒β b' → exf b ⇒β exf b'

inductive CBNs : Term → Term → Prop where
  | refl a : a ⇒β⋆ a
  | trans {a b c} : a ⇒β b → b ⇒β⋆ c → a ⇒β⋆ c
end

infix:40 "⇒β" => CBN
infix:40 "⇒β⋆" => CBNs

theorem CBNpar {a b} : a ⇒β b → a ⇒ b
  | CBN.β => Par.β (parRefl _) (parRefl _)
  | CBN.app rb => Par.app (CBNpar rb) (parRefl _)
  | CBN.exf rb => Par.exf (CBNpar rb)

@[simp] -- Shape of types of canonical values
def valueType {a} (A : Term) : Value a → Prop
  | Value.𝒰 | Value.pi | Value.mty | Value.lvl => ∃ k, 𝒰 k ≈ A
  | Value.abs => ∃ B C, pi B C ≈ A
  | Value.lof => ∃ k, lvl k ≈ A

-- The types of canonical values have the given shape
theorem wtValue {a A B : Term} (h : ⬝ ⊢ a ∶ A) (e : A ≈ B) : (v : Value a) → valueType B v
  | Value.𝒰 => let ⟨_, e𝒰⟩ := wtf𝒰Inv h; ⟨_, Eqv.trans e𝒰 e⟩
  | Value.pi => let ⟨_, e𝒰⟩ := wtfPiInv𝒰 h; ⟨_, Eqv.trans e𝒰 e⟩
  | Value.abs => let ⟨_, _, _, epi⟩ := wtfAbsInv h; ⟨_, _, Eqv.trans epi e⟩
  | Value.mty => let ⟨_, e𝒰⟩ := wtfMtyInv h; ⟨_, Eqv.trans e𝒰 e⟩
  | Value.lvl => let ⟨_, _, _, e𝒰⟩ := wtfLvlInv h; ⟨_, Eqv.trans e𝒰 e⟩
  | Value.lof => let ⟨_, elvl⟩ := wtfLofInv h; ⟨_, Eqv.trans elvl e⟩

theorem wtAbs {b A B : Term} (v : Value b) (h : ⬝ ⊢ b ∶ pi A B) : ∃ b', b = abs b' := by
  generalize e : @Sigma.mk I idx I.wt ⟨⬝, b, pi A B⟩ = t at h
  induction h generalizing b A B
  all_goals injection e with eI e; injection eI
  all_goals injection e with eCtxt eTerm eType;
            subst eCtxt; subst eTerm
  all_goals try first | contradiction | subst eType | injection eType
  case abs eA eB => subst eA eB; exact ⟨_, rfl⟩
  case conv h _ epi _ _ =>
    let ee := wtValue h epi v
    cases v <;> let ⟨_, e⟩ := ee
    case 𝒰 | pi | mty | lvl => cases conv𝒰Pi (eqvConv e)
    case abs => exact ⟨_, rfl⟩
    case lof => cases convLvlPi (eqvConv e)

theorem wtMty {b : Term} (v : Value b) (h : ⬝ ⊢ b ∶ mty) : False := by
  generalize e : @Sigma.mk I idx I.wt ⟨⬝, b, mty⟩ = t at h
  induction h generalizing b
  all_goals injection e with eI e; injection eI
  all_goals injection e with eCtxt eTerm eType;
            subst eCtxt; subst eTerm
  all_goals try first | contradiction | subst eType
  case conv h _ emty _ _ =>
    let ee := wtValue h emty v
    cases v <;> let ⟨_, e⟩ := ee
    case 𝒰 | pi | mty | lvl => cases conv𝒰Mty (eqvConv e)
    case abs => let ⟨_, e⟩ := e; cases convMtyPi (eqvConv (Eqv.sym e))
    case lof => cases convLvlMty (eqvConv e)

theorem wtProgress {a A : Term} (h : ⬝ ⊢ a ∶ A) : Nonempty (Value a) ∨ ∃ b, a ⇒β b := by
  generalize e : @Sigma.mk I idx I.wt ⟨⬝, a, A⟩ = t at h
  induction h generalizing a A
  all_goals injection e with eI e; injection eI
  all_goals injection e with eCtxt eTerm eType;
            subst eCtxt; subst eTerm; subst eType
  case var mem => cases mem
  case 𝒰 | pi | abs | mty | lvl | lof => repeat constructor
  case trans ih | conv ih _ _ _ | sub ih => exact ih rfl
  case app hb _ ihb _ =>
    cases ihb rfl
    case inl v =>
      cases v with | intro v =>
      let ⟨_, e⟩ := wtAbs v hb; subst e
      exact Or.inr ⟨_, CBN.β⟩
    case inr r => let ⟨_, r⟩ := r; exact Or.inr ⟨_, CBN.app r⟩
  case exf hb ihb _ _ =>
    cases ihb rfl
    case inl v => cases v with | intro v => cases wtMty v hb
    case inr r => let ⟨_, r⟩ := r; exact Or.inr ⟨_, CBN.exf r⟩

/-*-------
  Safety
-------*-/

theorem wtSafety {a b A : Term} (h : ⬝ ⊢ a ∶ A) (r : a ⇒β⋆ b) :
  Nonempty (Value b) ∨ ∃ c, b ⇒β c := by
  induction r
  case refl => exact wtProgress h
  case trans r _ ih => exact ih (wtPar (CBNpar r) h)
