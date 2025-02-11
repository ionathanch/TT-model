import «src».safety
import «src».normalization

open Term
open Nat

set_option autoImplicit false
set_option pp.fieldNotation false

variable [lc : LevelClass]

-- Normal forms do not reduce
theorem nfCBN {a b} (nfa : nf a) (r : a ⇒β b) : False := by
  induction r <;> simp at *
  case app ih => let ⟨neb, _⟩ := nfa; exact ih (neNf neb)
  case exf ih => let ⟨_, neb⟩ := nfa; exact ih (neNf neb)

-- Forward preservation of values
theorem valuePars {a b} (r : a ⇒⋆ b) (v : Value a) : Nonempty (Value b) := by
  cases v
  case 𝒰 => let ⟨_, e, _⟩ := pars𝒰Inv r; subst e; constructor; constructor
  case pi => let ⟨_, _, e, _⟩ := parsPiInv r; subst e; constructor; constructor
  case abs => let ⟨_, _, e, _⟩ := parsAbsInv r; subst e; constructor; constructor
  case mty => have e := parsMtyInv r; subst e; constructor; constructor
  case lvl => let ⟨_, e, _⟩ := parsLvlInv r; subst e; constructor; constructor
  case lof => have e := parsLofInv r; subst e; constructor; constructor

-- Closed terms evaluate to a value
theorem evaluation {a A : Term} (h : ⬝ ⊢ a ∶ A) : ∃ b, a ⇒⋆ b ∧ Nonempty (Value b) := by
  match normalization h with
  | ⟨⟨b, nfb, r⟩, _⟩ =>
    let hb := wtPars r h
    cases wtProgress hb
    case inl => exists b
    case inr h => let ⟨_, r⟩ := h; cases nfCBN nfb r

-- Closed terms are not open, i.e. weak neutral
theorem closed {a A : Term} (h : ⬝ ⊢ a ∶ A) : ¬ wne a
  | ⟨b, neb, rb⟩ => by
    let ⟨c, rc, ⟨vc⟩⟩ := evaluation h
    let ⟨d, rbd, rcd⟩ := confluence rb rc
    let _ := nePars rbd neb
    let ⟨ve⟩ := valuePars rcd vc
    cases ve <;> contradiction

/-*-----------------------------------------
  Canonicity corollaries for closed terms:
  * Empty type is uninhabited
  * Universes contain types
  * Level terms are internalized levels
-----------------------------------------*-/

theorem consistency {b} : ¬ ⬝ ⊢ b ∶ mty := by
  intro h
  let ⟨_, _, hmty, hb⟩ := soundness h var (semSubstNil _)
  simp [interpsMtyInv hmty, substId] at hb
  exact closed h hb

theorem canon𝒰 {T j} (h : ⬝ ⊢ T ∶ 𝒰 j) :
  (∃ A B, T ⇒⋆ pi A B) ∨
  (∃ i, T ⇒⋆ 𝒰 i) ∨
  (T ⇒⋆ mty) ∨
  (∃ b, T ⇒⋆ lvl b) := by
  let ⟨_, _, h𝒰, hT⟩ := soundness h var (semSubstNil _)
  let ⟨_, _, _, e⟩ := interps𝒰Inv h𝒰; subst e
  let ⟨_, hT⟩ := hT; rw [substId] at hT
  cases interpsStepInv hT
  case inl wneT => cases closed h wneT
  case inr h => exact h

theorem canonLvl {a k} (h : ⬝ ⊢ a ∶ lvl k) : ∃ j, a ⇒⋆ lof j := by
  let ⟨_, _, hlvl, ha⟩ := soundness h var (semSubstNil _)
  let ⟨_, e⟩ := interpsLvlInv hlvl; subst e
  rw [substId] at ha
  cases ha
  case inl ha => let ⟨_, _, _, r, _⟩ := ha; exact ⟨_, r⟩
  case inr wnea => cases closed h wnea
