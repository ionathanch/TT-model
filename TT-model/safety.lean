import «TT-model».typing

open Nat
open Term

set_option autoImplicit false
set_option pp.fieldNotation false

variable [LevelClass]

/-*------------------------------
  Renaming and weakening lemmas
------------------------------*-/

theorem wtRename {ξ : ℕ → ℕ} {Γ Δ} {a A : Term}
  (hξ : Δ ⊢ ξ ∶ Γ) (hΔ : ⊢ Δ) (h : Γ ⊢ a ∶ A) :
  Δ ⊢ rename ξ a ∶ rename ξ A := by
  induction h using wtInd generalizing ξ Δ
  case var => constructor; assumption; apply_rules [hξ]
  case 𝒰 ih => exact Wtf.𝒰 (ih hξ hΔ)
  case pi ihA ihB =>
    let ihA' := ihA hξ hΔ
    refine Wtf.pi ihA' ?_
    rw [renameLiftRename]
    exact ihB (wRenameLift hξ) (Wtf.cons hΔ ihA')
  case abs ihPi ihb =>
    let ihPi' := ihPi hξ hΔ
    refine Wtf.abs ihPi' ?_
    let ⟨k, hA⟩ := wtfPiInvA ihPi'
    exact ihb (wRenameLift hξ) (Wtf.cons hΔ hA)
  case app ihb iha => rw [← renameDist]; exact Wtf.app (ihb hξ hΔ) (iha hξ hΔ)
  case mty ih => exact Wtf.mty (ih hξ hΔ)
  case exf ihb ihA => exact Wtf.exf (ihb hξ hΔ) (ihA hξ hΔ)
  case lvl iha ihj => exact Wtf.lvl (iha hξ hΔ) (ihj hξ hΔ)
  case lof => constructor <;> assumption
  case trans ihi ihj => exact Wtf.trans (ihi hξ hΔ) (ihj hξ hΔ)
  case conv e _ _ iha ihA =>
    exact Wtf.conv (convEqv (convRename ξ (eqvConv e))) (iha hξ hΔ) (ihA hξ hΔ)
  case sub ihj ihA => exact Wtf.sub (ihj hξ hΔ) (ihA hξ hΔ)

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
  induction h using wtInd generalizing σ Δ
  case var mem => exact hσ _ _ mem
  case 𝒰 ih => exact Wtf.𝒰 (ih hσ hΔ)
  case pi ihA ihB =>
    let ihA' := ihA hσ hΔ
    refine Wtf.pi ihA' ?_
    rw [renameUpSubst]
    exact ihB (wSubstUp ihA' hσ) (Wtf.cons hΔ ihA')
  case abs ihPi ihb =>
    let ihPi' := ihPi hσ hΔ
    let ⟨k, hA⟩ := wtfPiInvA ihPi'
    exact Wtf.abs ihPi' (ihb (wSubstUp hA hσ) (Wtf.cons hΔ hA))
  case app ihb iha => rw [← substDist]; exact Wtf.app (ihb hσ hΔ) (iha hσ hΔ)
  case mty ih => exact Wtf.mty (ih hσ hΔ)
  case exf ihb ihA => exact Wtf.exf (ihb hσ hΔ) (ihA hσ hΔ)
  case lvl iha ihj => exact Wtf.lvl (iha hσ hΔ) (ihj hσ hΔ)
  case lof => constructor <;> assumption
  case trans ihi ihj => exact Wtf.trans (ihi hσ hΔ) (ihj hσ hΔ)
  case conv e _ _ iha ihA =>
    refine Wtf.conv (convEqv (convSubst σ (eqvConv e))) (iha hσ hΔ) (ihA hσ hΔ)
  case sub ihj ihA => exact Wtf.sub (ihj hσ hΔ) (ihA hσ hΔ)

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
  induction h using wtInd
  case var wf mem => exact wtMem mem wf
  case pi ih _ | trans ih => exact ih
  case abs h _ _ _ | exf h _ _ _ | conv h _ _ => exact ⟨_, h⟩
  case 𝒰 ih =>
    let ⟨_, ihk⟩ := ih
    let ⟨l, _, hk, _⟩ := wtfLvlInv ihk
    exact ⟨l, Wtf.𝒰 hk⟩
  case app ha ihb _ =>
    let ⟨_, hPi⟩ := ihb
    let ⟨k, hB⟩ := wtfPiInvB hPi
    exact ⟨subst _ k, wtSubst ha hB⟩
  case mty hj _ => exact ⟨_, hj⟩
  case lvl hj _ _ => exact ⟨_, hj⟩
  case lof k wf _ =>
    let ⟨l, klgt⟩ := exists_gt k
    let ⟨m, lmgt⟩ := exists_gt l
    refine ⟨lof l, ?_⟩
    apply Wtf.lvl (Wtf.lof wf klgt)
    apply Wtf.𝒰 (Wtf.lof wf lmgt)
  case sub ih _ =>
    let ⟨_, ihk⟩ := ih
    let ⟨l, _, hk, _⟩ := wtfLvlInv ihk
    exact ⟨l, Wtf.𝒰 hk⟩

/-*-------------
  Preservation
-------------*-/

theorem wtPar {Γ} {a b A : Term} (r : a ⇒ b) (h : Γ ⊢ a ∶ A) : Γ ⊢ b ∶ A := by
  induction h using wtInd generalizing b
  case var => cases r; constructor <;> assumption
  case 𝒰 ih => cases r with | 𝒰 r' => exact Wtf.𝒰 (ih r')
  case pi ihA ihB =>
    cases r with | pi ra rb =>
    let ihA' := ihA ra
    exact Wtf.pi ihA' (wtReplace (parEqv ra) ihA' (ihB rb))
  case abs hPi _ _ ihb => cases r with | abs r' => exact Wtf.abs hPi (ihb r')
  case app hb ha ihb iha =>
    cases r
    case β rb ra =>
      let ⟨_, hA⟩ := wtRegularity ha
      let ⟨_, hPi⟩ := wtRegularity hb
      let ⟨_, hB⟩ := wtfPiInvB hPi
      let ⟨A', B', hb', e⟩ := wtfAbsInv (ihb (Par.abs rb))
      let ⟨eA, eB⟩ := convPiInv (eqvConv e)
      exact Wtf.conv
        (convEqv (convCong (convSym (parConv ra)) eB))
        (wtSubst (iha ra) (wtReplace (convEqv eA) hA hb'))
        (wtSubst ha hB)
    case app rb ra =>
      let ⟨k, hBa⟩ := wtRegularity (Wtf.app hb ha)
      exact Wtf.conv
        (convEqv (convSym (parConv (parCong ra (parRefl _)))))
        (Wtf.app (ihb rb) (iha ra)) hBa
  case mty ih => cases r; exact Wtf.mty (ih (parRefl _))
  case exf hA _ _ ihb => cases r with | exf r' => exact Wtf.exf hA (ihb r')
  case lvl hj iha _ => cases r with | lvl r' => exact Wtf.lvl (iha r') hj
  case lof => cases r; constructor <;> assumption
  case trans hj ihi _ => exact Wtf.trans (ihi r) hj
  case conv e _ hB iha _ => exact Wtf.conv e (iha r) hB
  case sub hj _ _ ihA => exact Wtf.sub hj (ihA r)

theorem wtPars {Γ} {a b A : Term} (r : a ⇒⋆ b) (h : Γ ⊢ a ∶ A) : Γ ⊢ b ∶ A := by
  induction r
  case refl => exact h
  case trans r _ ih => exact ih (wtPar r h)

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
theorem wtValue {Γ} {a A B : Term} (h : Γ ⊢ a ∶ A) (e : A ≈ B) : (v : Value a) → valueType B v
  | Value.𝒰 => let ⟨_, e𝒰⟩ := wtf𝒰Inv h; ⟨_, Eqv.trans e𝒰 e⟩
  | Value.pi => let ⟨_, e𝒰⟩ := wtfPiInv𝒰 h; ⟨_, Eqv.trans e𝒰 e⟩
  | Value.abs => let ⟨_, _, _, epi⟩ := wtfAbsInv h; ⟨_, _, Eqv.trans epi e⟩
  | Value.mty => let ⟨_, e𝒰⟩ := wtfMtyInv h; ⟨_, Eqv.trans e𝒰 e⟩
  | Value.lvl => let ⟨_, _, _, e𝒰⟩ := wtfLvlInv h; ⟨_, Eqv.trans e𝒰 e⟩
  | Value.lof => let ⟨_, elvl⟩ := wtfLofInv h; ⟨_, Eqv.trans elvl e⟩

theorem wtAbs {Γ} {b A B : Term} (v : Value b) (h : Γ ⊢ b ∶ pi A B) : ∃ b', b = abs b' := by
  generalize e : pi A B = T at h
  induction h using wtInd
  all_goals try first | subst e | injection e
  case var | app | exf => contradiction
  case abs => exact ⟨_, rfl⟩
  case conv h v epi _ _ =>
    let _e := wtValue h epi v
    cases v <;> let ⟨_, e⟩ := _e
    case 𝒰 | pi | mty | lvl => cases conv𝒰Pi (eqvConv e)
    case abs => exact ⟨_, rfl⟩
    case lof => cases convLvlPi (eqvConv e)

theorem wtMty {Γ} {b : Term} (v : Value b) (h : Γ ⊢ b ∶ mty) : False := by
  generalize e : mty = T at h
  induction h using wtInd
  all_goals try first | subst e | injection e
  case var | app | exf => contradiction
  case conv h v emty _ _ =>
    let _e := wtValue h emty v
    cases v <;> let ⟨_, e⟩ := _e
    case 𝒰 | pi | mty | lvl => cases conv𝒰Mty (eqvConv e)
    case abs => let ⟨_, e⟩ := e; cases convMtyPi (eqvConv (Eqv.sym e))
    case lof => cases convLvlMty (eqvConv e)

theorem wtProgress {a A : Term} (h : ⬝ ⊢ a ∶ A) : Nonempty (Value a) ∨ ∃ b, a ⇒β b := by
  generalize e : (⬝) = Γ at h
  induction h using wtInd
  all_goals subst e; specialize_rfls
  case var mem => cases mem
  case 𝒰 | pi | abs | mty | lvl | lof => repeat constructor
  case trans ih _ | conv ih _ | sub ih => exact ih
  case app hb _ ihb _ =>
    cases ihb
    case inl v =>
      cases v with | intro v =>
      let ⟨_, e⟩ := wtAbs v hb; subst e
      exact Or.inr ⟨_, CBN.β⟩
    case inr r => let ⟨_, r⟩ := r; exact Or.inr ⟨_, CBN.app r⟩
  case exf _ hb _ ihb =>
    cases ihb
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
