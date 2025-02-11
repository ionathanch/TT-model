import «src».reduction

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
  | abs a b => nf a ∧ nf b
  | app b a => ne b ∧ nf a
  | exf a b => nf a ∧ ne b
  | lvl a => nf a
  | _ => True

@[simp]
def ne : Term → Prop
  | var _ => True
  | app b a => ne b ∧ nf a
  | exf a b => nf a ∧ ne b
  | _ => False
end

theorem neNf {a} : ne a → nf a := by
  induction a <;> unfold ne nf <;> simp
  case app =>
    intro neb nfa
    unfold nf
    exact ⟨neb, nfa⟩
  case exf =>
    intro nfa neb
    unfold nf
    exact ⟨nfa, neb⟩

/-*---------------------------------------------------
  Normal and neutral forms are stable under renaming
  (both directions hold but we only need one)
---------------------------------------------------*-/

mutual
theorem nfRename {ξ a} (nfa : nf (rename ξ a)) : nf a := by
  cases a <;> simp at *
  case 𝒰 | lvl => exact nfRename nfa
  case pi | abs => let ⟨nfa, nfb⟩ := nfa; exact ⟨nfRename nfa, nfRename nfb⟩
  case app => let ⟨nfb, nfa⟩ := nfa; exact ⟨neRename nfb, nfRename nfa⟩
  case exf => let ⟨nfa, neb⟩ := nfa; exact ⟨nfRename nfa, neRename neb⟩

theorem neRename {ξ a} (nfa : ne (rename ξ a)) : ne a := by
  cases a <;> simp at *
  case app => let ⟨neb, nfa⟩ := nfa; exact ⟨neRename neb, nfRename nfa⟩
  case exf => let ⟨nfa, neb⟩ := nfa; exact ⟨nfRename nfa, neRename neb⟩
end

/-*-------------------------------------------------
  Forward preservation of normal and neutral forms
-------------------------------------------------*-/

mutual
theorem nfPar {a b} (r : a ⇒ b) : nf a → nf b := by
  cases r <;> simp <;> intros
  case 𝒰 ra nfa | lvl ra nfa => exact nfPar ra nfa
  case pi ra rb nfa nfb | abs ra rb nfa nfb => exact ⟨nfPar ra nfa, nfPar rb nfb⟩
  case app rb ra neb nfa => exact ⟨nePar rb neb, nfPar ra nfa⟩
  case exf ra rb nfa neb => exact ⟨nfPar ra nfa, nePar rb neb⟩

theorem nePar {a b} (r : a ⇒ b) : ne a → ne b := by
  cases r <;> simp <;> intros
  case app rb ra neb nfa => exact ⟨nePar rb neb, nfPar ra nfa⟩
  case exf ra rb nfa neb => exact ⟨nfPar ra nfa, nePar rb neb⟩
end

theorem nfPars {a b} (r : a ⇒⋆ b) : nf a → nf b := by
  induction r
  case refl => simp
  case trans ra _ ih => intro nfa; exact ih (nfPar ra nfa)

theorem nePars {a b} (r : a ⇒⋆ b) : ne a → ne b := by
  induction r
  case refl => simp
  case trans ra _ ih => intro nfa; exact ih (nePar ra nfa)

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

/-*----------------------------------------------------
  Weak normal/neutral forms are stable under renaming
----------------------------------------------------*-/

theorem wnfRename {ξ a} : wnf (rename ξ a) → wnf a
  | ⟨b, nfb, rb⟩ => by
    let ⟨c, e, r⟩ := parsAntirenaming rb; subst e
    exact ⟨c, nfRename nfb, r⟩

theorem wneRename {ξ a} : wne (rename ξ a) → wne a
  | ⟨b, neb, rb⟩ => by
    let ⟨c, e, r⟩ := parsAntirenaming rb; subst e
    exact ⟨c, neRename neb, r⟩

/-*-----------------------------------------------------------
  Forward/backward preservation of weak normal/neutral forms
-----------------------------------------------------------*-/

theorem wnfBwds {a b} (r : a ⇒⋆ b) : wnf b → wnf a
  | ⟨c, nfc, rc⟩ => ⟨c, nfc, parsTrans r rc⟩

theorem wneBwds {a b} (r : a ⇒⋆ b) : wne b → wne a
  | ⟨c, nec, rc⟩ => ⟨c, nec, parsTrans r rc⟩

theorem wnfFwds {a b} (r : a ⇒⋆ b) : wnf a → wnf b
  | ⟨c, nfc, rc⟩ => by
    let ⟨d, rbd, rcd⟩ := confluence r rc
    refine ⟨d, nfPars rcd nfc, rbd⟩

theorem wneFwds {a b} (r : a ⇒⋆ b) : wne a → wne b
  | ⟨c, nec, rc⟩ => by
    let ⟨d, rbd, rcd⟩ := confluence r rc
    refine ⟨d, nePars rcd nec, rbd⟩

/-*-------------------------------------------
  Constructors for weak normal/neutral forms
-------------------------------------------*-/

theorem wneVar {s} : wne (var s) :=
  ⟨var s, ⟨⟩, Pars.refl _⟩

theorem wnfPi {a b} (wnfa : wnf a) (wnfb : wnf b) : wnf (pi a b) :=
  let ⟨a', nfa, ra⟩ := wnfa
  let ⟨b', nfb, rb⟩ := wnfb
  ⟨pi a' b', ⟨nfa, nfb⟩, parsPi ra rb⟩

theorem wnfAbs {a b} (wnfa : wnf a) (wnfb : wnf b) : wnf (abs a b) :=
  let ⟨a', nfa, ra⟩ := wnfa
  let ⟨b', nfb, rb⟩ := wnfb
  ⟨abs a' b', ⟨nfa, nfb⟩, parsAbs ra rb⟩

theorem wneApp {b a} (wneb : wne b) (wnfa : wnf a) : wne (app b a) :=
  let ⟨b', neb, rb⟩ := wneb
  let ⟨a', nfa, ra⟩ := wnfa
  ⟨app b' a', ⟨neb, nfa⟩, parsApp rb ra⟩

theorem wnf𝒰 {b} (wnfb : wnf b) : wnf (𝒰 b) :=
  let ⟨c, nfc, rc⟩ := wnfb
  ⟨𝒰 c, nfc, pars𝒰 rc⟩

theorem wneExf {a b} (wnfa : wnf a) (wneb : wne b) : wne (exf a b) :=
  let ⟨a', nfa, ra⟩ := wnfa
  let ⟨b', neb, rb⟩ := wneb
  ⟨exf a' b', ⟨nfa, neb⟩, parsExf ra rb⟩

theorem wnfLvl {b} (wnfb : wnf b) : wnf (lvl b) :=
  let ⟨c, nfc, rc⟩ := wnfb
  ⟨lvl c, nfc, parsLvl rc⟩

theorem wnfLof {k} : wnf (lof k) := ⟨lof k, ⟨⟩, Pars.refl _⟩

theorem wneLof {a j} (r : a ⇒⋆ lof j) (wnea : wne a) : False :=
  match wneFwds r wnea with
  | ⟨b, neb, rb⟩ => by rw [parsLofInv rb] at neb; simp at neb

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
        exact wnfAbs sorry ⟨c, nfRename nfc, rb⟩
      case app rb ra ih =>
        cases ra
        apply wnfBwds (parPars rb) (ih nfc rfl)
