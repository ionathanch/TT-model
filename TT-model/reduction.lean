import «TT-model».syntactics

open Term

set_option autoImplicit false
set_option pp.fieldNotation false

variable [LevelClass]

/-*-------------------
  Parallel reduction
-------------------*-/

section
set_option hygiene false
local infix:40 "⇒" => Par

inductive Par : Term → Term → Prop where
  | β {b b' a a'} :
    b ⇒ b' →
    a ⇒ a' →
    ------------------------------------
    app (abs b) a ⇒ subst (a' +: var) b'
  | var s : var s ⇒ var s
  | 𝒰 {a a'} :
    a ⇒ a' →
    ------------
    𝒰 a ⇒ 𝒰 a'
  | pi {a a' b b'} :
    a ⇒ a' →
    b ⇒ b' →
    -----------------
    pi a b ⇒ pi a' b'
  | abs {b b'} :
    b ⇒ b' →
    --------------
    abs b ⇒ abs b'
  | app {b b' a a'} :
    b ⇒ b' →
    a ⇒ a' →
    -------------------
    app b a ⇒ app b' a'
  | mty : mty ⇒ mty
  | exf {b b'} :
    b ⇒ b' →
    --------------
    exf b ⇒ exf b'
  | lvl {a a'} :
    a ⇒ a' →
    --------------
    lvl a ⇒ lvl a'
  | lof k : lof k ⇒ lof k
end

infix:40 "⇒" => Par

theorem parRefl a : a ⇒ a := by
  induction a <;> constructor <;> assumption

theorem parRename {a b} ξ (r : a ⇒ b) : rename ξ a ⇒ rename ξ b := by
  induction r generalizing ξ <;> try constructor
  case β ihb iha => rw [← renameDist]; constructor; apply ihb; apply iha
  all_goals apply_assumption

theorem parLift σ τ (h : ∀ x, σ x ⇒ τ x) : ∀ x, (⇑ σ) x ⇒ (⇑ τ) x := by
  intro n; cases n
  case zero => constructor
  case succ n => apply parRename; apply h

theorem parMorphing {a b} σ τ (h : ∀ x, σ x ⇒ τ x) (r : a ⇒ b) : subst σ a ⇒ subst τ b := by
  induction r generalizing σ τ h <;> try constructor
  case β ihb iha =>
    rw [← substDist]; constructor
    all_goals apply_rules [parLift]
  all_goals apply_rules [parLift]

theorem parSubst {a b} σ (r : a ⇒ b) : subst σ a ⇒ subst σ b := by
  apply parMorphing (r := r); intros; apply parRefl

theorem parCong {a a' b b'} (ra : a ⇒ a') (rb : b ⇒ b') : subst (a +: var) b ⇒ subst (a' +: var) b' := by
  apply parMorphing (r := rb); intro n; cases n <;> first | assumption | constructor

/-*----------------------------------------------------
  Reflexive, transitive closure of parallel reduction
----------------------------------------------------*-/

section
set_option hygiene false
local infix:40 "⇒⋆" => Pars

inductive Pars : Term → Term → Prop where
  | refl a : a ⇒⋆ a
  | trans {a b c} : a ⇒ b → b ⇒⋆ c → a ⇒⋆ c
end

infix:40 "⇒⋆" => Pars
open Pars

theorem parPars {a b} (r : a ⇒ b) : a ⇒⋆ b := by
  constructor; assumption; constructor

theorem parsTrans {a b c} (r₁ : a ⇒⋆ b) (r₂ : b ⇒⋆ c) : a ⇒⋆ c := by
  induction r₁
  case refl => assumption
  case trans ih => constructor <;> apply_rules

theorem parsRename {a b} ξ (r : a ⇒⋆ b) : rename ξ a ⇒⋆ rename ξ b := by
  induction r <;> constructor
  all_goals apply_rules [parRename]

theorem parsSubst {a b} σ (r : a ⇒⋆ b) : subst σ a ⇒⋆ subst σ b := by
  induction r <;> constructor
  all_goals apply_rules [parSubst]

theorem parsCong {a a' b b'} (ra : a ⇒⋆ a') (rb : b ⇒⋆ b') : subst (a +: var) b ⇒⋆ subst (a' +: var) b' := by
  induction ra generalizing rb
  case refl => apply_rules [parsSubst]
  case trans ih => constructor <;> apply_rules [parCong, parRefl]

/-*------------------------------------------
  Constructors for parallel multi-reduction
------------------------------------------*-/

theorem pars𝒰 {a a'} (r : a ⇒⋆ a') : 𝒰 a ⇒⋆ 𝒰 a' := by
  induction r
  case refl => constructor
  case trans => constructor; constructor; assumption; assumption

theorem parsPi {a a' b b'} (ra : a ⇒⋆ a') (rb : b ⇒⋆ b') : pi a b ⇒⋆ pi a' b' := by
  induction ra generalizing b b' <;> induction rb
  case refl.refl => constructor
  case refl.trans ih =>
    constructor; constructor; apply parRefl; assumption; apply ih
  case trans.refl ih _ =>
    constructor; constructor; assumption; apply parRefl; apply ih; constructor
  case trans.trans ih _ _ _ _ _ _ =>
    constructor; constructor; assumption; assumption; apply ih; assumption

theorem parsAbs {b b'} (r : b ⇒⋆ b') : abs b ⇒⋆ abs b' := by
  induction r
  case refl => constructor
  case trans => constructor; constructor; assumption; assumption

theorem parsApp {a a' b b'} (rb : b ⇒⋆ b') (ra : a ⇒⋆ a') : app b a ⇒⋆ app b' a' := by
  induction rb generalizing a a' ra <;> induction ra
  case refl => constructor
  case refl.trans =>
    constructor; constructor; apply parRefl; assumption; assumption
  case trans.refl ih _ =>
    constructor; constructor; assumption; apply parRefl; apply ih; constructor
  case trans.trans ih _ _ _ _ _ _ =>
    constructor; constructor; assumption; assumption; apply ih; assumption

theorem parsExf {b b'} (r : b ⇒⋆ b') : exf b ⇒⋆ exf b' := by
  induction r
  case refl => constructor
  case trans => constructor; constructor; assumption; assumption

theorem parsLvl {a a'} (r : a ⇒⋆ a') : lvl a ⇒⋆ lvl a' := by
  induction r
  case refl => constructor
  case trans => constructor; constructor; assumption; assumption

theorem parsβ σ b a : app (abs (subst (⇑ σ) b)) a ⇒⋆ subst (a +: σ) b := by
  constructor
  . constructor; apply parRefl; apply parRefl
  . rw [← substUnion]; constructor

/-*--------------------------------------------------
  Inversion principles for parallel multi-reduction
--------------------------------------------------*-/

theorem pars𝒰Inv {a b} (r : 𝒰 a ⇒⋆ b) : ∃ a', b = 𝒰 a' ∧ a ⇒⋆ a' := by
  generalize e : 𝒰 a = c at r
  induction r generalizing a <;> subst e
  case refl => exists a; repeat constructor
  case trans ih r =>
    cases r with | 𝒰 r₁ =>
    let ⟨a', e, r₂⟩ := ih rfl
    exact ⟨a', e, trans r₁ r₂⟩

theorem parsMtyInv {b} (r : mty ⇒⋆ b) : b = mty := by
  generalize e : mty = a at r
  induction r
  case refl => rfl
  case trans r _ ih => subst e; cases r; simp [ih]

theorem parsPiInv {a b c} (r : pi a b ⇒⋆ c) : ∃ a' b', c = pi a' b' ∧ a ⇒⋆ a' ∧ b ⇒⋆ b' := by
  generalize e : pi a b = c' at r
  induction r generalizing a b <;> subst e
  case refl => exists a, b; repeat constructor
  case trans ih r =>
    cases r with | pi ra₁ rb₁ =>
    let ⟨a', b', e, ra₂, rb₂⟩ := ih rfl
    exact ⟨a', b', e, trans ra₁ ra₂, trans rb₁ rb₂⟩

theorem parsLvlInv {i b} (r : lvl i ⇒⋆ b) : ∃ j, b = lvl j ∧ i ⇒⋆ j := by
  generalize e : lvl i = a at r
  induction r generalizing i <;> subst e
  case refl => exists i; repeat constructor
  case trans ih r => cases r with | lvl rij =>
    let ⟨k, e, rjk⟩ := ih rfl
    exact ⟨k, e, trans rij rjk⟩

theorem parsLofInv {j b} (r : lof j ⇒⋆ b) : b = lof j := by
  generalize e : lof j = a at r
  induction r
  case refl => rfl
  case trans r _ ih => subst e; cases r; simp [ih]

/-*---------------------------------------
  Confluence via Takahashi's translation
---------------------------------------*-/

@[simp]
def taka : Term → Term
  | 𝒰 a => 𝒰 (taka a)
  | pi a b => pi (taka a) (taka b)
  | abs b => abs (taka b)
  | app b a => match b with
    | abs b => subst (taka a +: var) (taka b)
    | b => app (taka b) (taka a)
  | exf b => exf (taka b)
  | lvl a => lvl (taka a)
  | t => t

theorem parTaka {a b} (r : a ⇒ b) : b ⇒ taka a := by
  induction r
  any_goals unfold taka; (constructor <;> assumption)
  case β ihb iha => apply parCong <;> assumption
  case app r _ ih _ =>
    unfold taka; split
    . cases r; cases ih; apply Par.β <;> assumption
    . constructor <;> assumption

theorem diamond {a b c} (r₁ : a ⇒ b) (r₂ : a ⇒ c) : ∃ d, b ⇒ d ∧ c ⇒ d :=
  ⟨taka a, parTaka r₁, parTaka r₂⟩

/-*--------------------
      a
     / \
    b   c  by diamond
  // \ /
  d   e  by diacon
  \\ //
    f
--------------------*-/

theorem diacon {a b c} (r₁ : a ⇒⋆ b) (r₂ : a ⇒ c) : ∃ d, b ⇒⋆ d ∧ c ⇒⋆ d := by
  induction r₁ generalizing c
  case refl => exact ⟨c, parPars r₂, refl c⟩
  case trans a b d r₁ _ ih =>
    let ⟨e, r₃, r₄⟩ := diamond r₁ r₂
    let ⟨f, r₅, r₆⟩ := ih r₃
    exact ⟨f, r₅, trans r₄ r₆⟩

/-*---------------------------
     a
   //  \
  b     c  by diacon
   \\ // \\
     e     d  by confluence
      \\ //
        f
---------------------------*-/

theorem confluence {a b c} (r₁ : a ⇒⋆ b) (r₂ : a ⇒⋆ c) : ∃ d, b ⇒⋆ d ∧ c ⇒⋆ d := by
  induction r₂ generalizing b
  case refl => exact ⟨b, refl b, r₁⟩
  case trans a c d r₂ _ ih =>
    let ⟨e, r₃, r₄⟩ := diacon r₁ r₂
    let ⟨f, r₅, r₆⟩ := ih r₄
    exact ⟨f, parsTrans r₃ r₅, r₆⟩

/-*-----------
  Conversion
-----------*-/

def Conv (a : Term) (b : Term) : Prop := ∃ c, a ⇒⋆ c ∧ b ⇒⋆ c
infix:40 "⇔" => Conv

theorem parsConv {a b} (r : a ⇒⋆ b) : a ⇔ b :=
  ⟨b, r, refl b⟩

theorem parConv {a b} (r : a ⇒ b) : a ⇔ b :=
  parsConv (parPars r)

theorem convRefl {a} : a ⇔ a :=
  ⟨a, refl a, refl a⟩

theorem convSym {a b} : a ⇔ b → b ⇔ a
  | ⟨c, ra, rb⟩ => ⟨c, rb, ra⟩

theorem convTrans {a b c} : a ⇔ b → b ⇔ c → a ⇔ c
  | ⟨_, rac, rbc⟩, ⟨_, rbd, rcd⟩ =>
  let ⟨e, rce, rde⟩ := confluence rbc rbd
  ⟨e, parsTrans rac rce, parsTrans rcd rde⟩

theorem convRename {a b} ξ : a ⇔ b → rename ξ a ⇔ rename ξ b
  | ⟨c, ra, rb⟩ => ⟨rename ξ c, parsRename ξ ra, parsRename ξ rb⟩

theorem convSubst {a b} σ : a ⇔ b → subst σ a ⇔ subst σ b
  | ⟨c, ra, rb⟩ => ⟨subst σ c, parsSubst σ ra, parsSubst σ rb⟩

theorem convCong {a a' b b'} : a ⇔ a' → b ⇔ b' → subst (a +: var) b ⇔ subst (a' +: var) b'
  | ⟨a'', ra, ra'⟩, ⟨b'', rb, rb'⟩ =>
  ⟨subst (a'' +: var) b'', parsCong ra rb, parsCong ra' rb'⟩

/-*----------------------------
  Constructors for conversion
----------------------------*-/

theorem conv𝒰 {a a'} : a ⇔ a' → 𝒰 a ⇔ 𝒰 a'
  | ⟨a'', ra, ra'⟩ => ⟨𝒰 a'', pars𝒰 ra, pars𝒰 ra'⟩

theorem convPi {a a' b b'} : a ⇔ a' → b ⇔ b' → pi a b ⇔ pi a' b'
  | ⟨a'', ra, ra'⟩, ⟨b'', rb, rb'⟩ =>
  ⟨pi a'' b'', parsPi ra rb, parsPi ra' rb'⟩

theorem convAbs {b b'} : b ⇔ b' → abs b ⇔ abs b'
  | ⟨b'', rb, rb'⟩ => ⟨abs b'', parsAbs rb, parsAbs rb'⟩

theorem convApp {b b' a a'} : b ⇔ b' → a ⇔ a' → app b a ⇔ app b' a'
  | ⟨b'', rb, rb'⟩, ⟨a'', ra, ra'⟩ =>
  ⟨app b'' a'', parsApp rb ra, parsApp rb' ra'⟩

theorem convExf {b b'} : b ⇔ b' → exf b ⇔ exf b'
  | ⟨b'', rb, rb'⟩ => ⟨exf b'', parsExf rb, parsExf rb'⟩

theorem convLvl {a a'} : a ⇔ a' → lvl a ⇔ lvl a'
  | ⟨a'', ra, ra'⟩ => ⟨lvl a'', parsLvl ra, parsLvl ra'⟩

/-*------------------------------------
  Inversion principles for conversion
------------------------------------*-/

theorem conv𝒰Mty {a} : ¬ 𝒰 a ⇔ mty
  | ⟨_, r𝒰, rmty⟩ =>
  let ⟨_, e𝒰, _⟩ := pars𝒰Inv r𝒰
  have emty := parsMtyInv rmty
  by subst emty; contradiction

theorem conv𝒰Pi {c a b} : ¬ 𝒰 c ⇔ pi a b
  | ⟨_, r𝒰, rpi⟩ =>
  let ⟨_, e𝒰, _⟩ := pars𝒰Inv r𝒰
  let ⟨_, _, epi, _, _⟩ := parsPiInv rpi
  by subst epi; contradiction

theorem convMtyPi {a b} : ¬ mty ⇔ pi a b
  | ⟨_, rmty, rpi⟩ =>
  let ⟨_, _, epi, _, _⟩ := parsPiInv rpi
  have emty := parsMtyInv rmty
  by subst epi; contradiction

theorem convLvlPi {a b k} : ¬ lvl k ⇔ pi a b
  | ⟨_, rlvl, rpi⟩ =>
  let ⟨_, _, epi, _, _⟩ := parsPiInv rpi
  have ⟨_, e, _⟩ := parsLvlInv rlvl
  by subst epi; contradiction

theorem conv𝒰Inv {a b} : 𝒰 a ⇔ 𝒰 b → a ⇔ b
  | ⟨_, ra, rb⟩ =>
  let ⟨a, e𝒰a, ra'⟩ := pars𝒰Inv ra
  let ⟨b, e𝒰b, rb'⟩ := pars𝒰Inv rb
  by subst e𝒰a; injection e𝒰b with eab; subst eab
     exact ⟨a, ra', rb'⟩

theorem convPiInv {a₁ a₂ b₁ b₂} : pi a₁ b₁ ⇔ pi a₂ b₂ → a₁ ⇔ a₂ ∧ b₁ ⇔ b₂
  | ⟨_, r₁, r₂⟩ =>
  let ⟨a₁', b₁', e₁, ra₁, rb₁⟩ := parsPiInv r₁
  let ⟨a₂', b₂', e₂, ra₂, rb₂⟩ := parsPiInv r₂
  by subst e₁; injection e₂ with ea eb
     subst ea; subst eb
     exact ⟨⟨a₁', ra₁, ra₂⟩, ⟨b₁', rb₁, rb₂⟩⟩
