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
  case 𝒰 | abs | lvl => exact nfRename nfa
  case pi => let ⟨nfa, nfb⟩ := nfa; exact ⟨nfRename nfa, nfRename nfb⟩
  case app => let ⟨nfb, nfa⟩ := nfa; exact ⟨neRename nfb, nfRename nfa⟩
  case exf => exact neRename nfa

theorem neRename {ξ a} (nfa : ne (rename ξ a)) : ne a := by
  cases a <;> simp at *
  case app => let ⟨neb, nfa⟩ := nfa; exact ⟨neRename neb, nfRename nfa⟩
  case exf => exact neRename nfa
end

-- Normal and neutral forms are forward closed by reduction
mutual
theorem nfPar {a b} (r : a ⇒ b) : nf a → nf b := by
  cases r <;> simp <;> intros
  case 𝒰 ra nfa | abs ra nfa | lvl ra nfa => exact nfPar ra nfa
  case pi ra rb nfa nfb => exact ⟨nfPar ra nfa, nfPar rb nfb⟩
  case app rb ra neb nfa => exact ⟨nePar rb neb, nfPar ra nfa⟩
  case exf rb neb => exact nePar rb neb

theorem nePar {a b} (r : a ⇒ b) : ne a → ne b := by
  cases r <;> simp <;> intros
  case app rb ra neb nfa => exact ⟨nePar rb neb, nfPar ra nfa⟩
  case exf rb neb => exact nePar rb neb
end

/-*------------------------------------------
  Weakly normal and neutral forms,
  i.e. existence of some parallel reduction
       to a normal or neutral form.
------------------------------------------*-/

@[simp] def wnf (a : Term) : Prop := ∃ b, nf b ∧ a ⇒⋆ b
@[simp] def wne (a : Term) : Prop := ∃ b, ne b ∧ a ⇒⋆ b

theorem wneWnf {a} : wne a → wnf a
  | ⟨b, neb, rb⟩ => ⟨b, neNf neb, rb⟩

theorem nfWnf {a} (nfa : nf a) : wnf a := ⟨a, nfa, Pars.refl a⟩
theorem neWne {a} (nea : ne a) : wne a := ⟨a, nea, Pars.refl a⟩

-- Weak normal forms are stable under renaming
theorem wnfRename {ξ a} : wnf (rename ξ a) → wnf a
  | ⟨b, nfb, rb⟩ => by
    let ⟨c, e, r⟩ := parsAntirenaming rb; subst e
    exact ⟨c, nfRename nfb, r⟩

-- Weak normal forms are backward closed by reduction
theorem wnfPar {a b} (r : a ⇒ b) : wnf b → wnf a
  | ⟨c, nfc, rc⟩ => ⟨c, nfc, Pars.trans r rc⟩

-- Weak neutral forms are backward closed by reduction
theorem wnePars {a b} (r : a ⇒⋆ b) : wne b → wne a
  | ⟨c, nec, rc⟩ => ⟨c, nec, parsTrans r rc⟩

/-*-------------------------------------------
  Constructors for weak normal/neutral forms
-------------------------------------------*-/

theorem wnfPi {a b} (wnfa : wnf a) (wnfb : wnf b) : wnf (pi a b) :=
  let ⟨a', nfa, ra⟩ := wnfa
  let ⟨b', nfb, rb⟩ := wnfb
  ⟨pi a' b', ⟨nfa, nfb⟩, parsPi ra rb⟩

theorem wnfAbs {b} (wnfb : wnf b) : wnf (abs b) :=
  let ⟨c, nfc, rc⟩ := wnfb
  ⟨abs c, nfc, parsAbs rc⟩

theorem wneApp {b a} (wneb : wne b) (wnfa : wnf a) : wne (app b a) :=
  let ⟨b', neb, rb⟩ := wneb
  let ⟨a', nfa, ra⟩ := wnfa
  ⟨app b' a', ⟨neb, nfa⟩, parsApp rb ra⟩

-- Inversion principle for weak normal applications to variables
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
