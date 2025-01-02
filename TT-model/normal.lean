import «TT-model».tactics
import «TT-model».syntactics
import «TT-model».reduction

open Term

set_option autoImplicit false
set_option pp.fieldNotation false

variable [LevelClass]

/-*-------------------------------------------------------
  Normal and neutral forms:
  * Normal forms are constructors with normal components
    and all neutral forms
  * Neutral forms are destructors with neutral heads
    and all variables
-------------------------------------------------------*-/

mutual
@[simp]
def nf : Term → Prop
  | 𝒰 a => nf a
  | pi a b => nf a ∧ nf b
  | abs b => nf b
  | app b a => ne b ∧ nf a
  | exf b => ne b
  | lvl a => nf a
  | _ => True

@[simp]
def ne : Term → Prop
  | var _ => True
  | app b a => ne b ∧ nf a
  | exf b => ne b
  | _ => False
end

theorem neNf {a} : ne a → nf a := by
  induction a <;> unfold ne nf <;> simp
  case app =>
    intro neb nfa
    unfold nf
    exact ⟨neb, nfa⟩

-- Normal and neutral forms are stable under renaming
-- (other direction also holds but is unneeded)
mutual
theorem nfRename {ξ a} (nfa : nf (rename ξ a)) : nf a := by
  cases a <;> simp at *
  case 𝒰 => exact nfRename nfa
  case pi => let ⟨nfa, nfb⟩ := nfa; exact ⟨nfRename nfa, nfRename nfb⟩
  case abs => exact nfRename nfa
  case app => let ⟨nfb, nfa⟩ := nfa; exact ⟨neRename nfb, nfRename nfa⟩
  case exf => exact neRename nfa
  case lvl => exact nfRename nfa

theorem neRename {ξ a} (nfa : ne (rename ξ a)) : ne a := by
  cases a <;> simp at *
  case app => let ⟨neb, nfa⟩ := nfa; exact ⟨neRename neb, nfRename nfa⟩
  case exf => exact neRename nfa
end

/-*------------------------------------------
  Weakly normal and neutral forms,
  i.e. existence of some parallel reduction
       to a normal or neutral form.
------------------------------------------*-/

@[simp] def wnf (a : Term) : Prop := ∃ b, nf b ∧ a ⇒⋆ b
@[simp] def wne (a : Term) : Prop := ∃ b, ne b ∧ a ⇒⋆ b

-- Weak normal forms are backwards closed by reduction
theorem wnfPar {a b} (r : a ⇒ b) : wnf b → wnf a
  | ⟨c, nfc, rc⟩ => ⟨c, nfc, Pars.trans r rc⟩

-- Constructor for weak normal forms
-- (other constructors are unneeded)
theorem wnfAbs {b} : wnf b → wnf (abs b)
  | ⟨c, nfc, rc⟩ => by
    exact ⟨abs c, nfc, parsAbs rc⟩

-- Inversion principle for weak normal forms
-- (other constructors are uneeded)
theorem wnfAppInv {b s} : wnf (app b (var s)) → wnf b
  | ⟨c, nfc, r⟩ => by
    generalize e : app b (var s) = b' at r
    induction r generalizing b; subst e
    case refl b =>
      let ⟨neb, _⟩ := nfc
      exact ⟨b, neNf neb, Pars.refl _⟩
    case trans b' c ra rb' _ =>
      subst e; cases ra
      case β rb ra _ =>
        cases ra
        rw [substToRename] at rb'
        have rb' := Pars.trans (parRename (s +: id) rb) rb'
        let ⟨c, e, rb⟩ := parsAntirenaming rb'; subst e
        exact wnfAbs ⟨c, nfRename nfc, rb⟩
      case app rb ra ih =>
        cases ra
        apply wnfPar rb (ih nfc rfl)
