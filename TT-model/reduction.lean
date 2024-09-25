import «TT-model».syntactics

open Nat
open Term

set_option autoImplicit false
set_option pp.fieldNotation false

variable [LevelClass]

/-*-------------------
  Parallel reduction
-------------------*-/

inductive I : Type where
  | pe : I
  | pt : I
open I

def idx : I → Type
  | pe => Unit
  | pt => Term × Term

section
set_option hygiene false
local notation:40 Γ:41 "⇒" Δ:41 => Par Γ Δ (Sigma.mk pe ())
local notation:40 Γ:41 "⊢" a:41 "⇒" Δ:41 "⊢" b:41 => Par Γ Δ (Sigma.mk pt ⟨a, b⟩)

inductive Par : Env → Env → (Σ w, idx w) → Prop where
  | nil : ⬝ ⇒ ⬝
  | cons {Γ Δ} :
    Γ ⇒ Δ →
    -----------
    Γ ∷_ ⇒ Δ ∷_
  | dcons {Γ Δ a a'} :
    Γ ⇒ Δ →
    Γ ⊢ a ⇒ Δ ⊢ a' →
    ----------------
    Γ ∷ᵈ a ⇒ Δ ∷ᵈ a'
  | β {Γ Δ b b' a a'} :
    Γ ⇒ Δ →
    Γ ∷_ ⊢ b ⇒ Δ ∷_ ⊢ b' →
    Γ ⊢ a ⇒ Δ ⊢ a' →
    --------------------------------------------
    Γ ⊢ app (abs b) a ⇒ Δ ⊢ subst (a' +: var) b'
  | ζ {Γ Δ a a' b b'} :
    Γ ⇒ Δ →
    Γ ⊢ a ⇒ Δ ⊢ a' →
    Γ ∷_ ⊢ b ⇒ Δ ∷_ ⊢ b' →
    ----------------------------------------
    Γ ⊢ letin a b ⇒ Δ ⊢ subst (a' +: var) b'
  | var {Γ Δ} s :
    Γ ⇒ Δ →
    ---------------------
    Γ ⊢ var s ⇒ Δ ⊢ var s
  | δ {Γ Δ x a} :
    Γ ⇒ Δ →
    Δ ∋ x ≔ a →
    -----------------
    Γ ⊢ var x ⇒ Δ ⊢ a
  | 𝒰 {Γ Δ a a'} :
    Γ ⇒ Δ →
    Γ ⊢ a ⇒ Δ ⊢ a' →
    -------------------
    Γ ⊢ 𝒰 a ⇒ Δ ⊢ 𝒰 a'
  | pi {Γ Δ a a' b b'} :
    Γ ⇒ Δ →
    Γ ⊢ a ⇒ Δ ⊢ a' →
    Γ ∷_ ⊢ b ⇒ Δ ∷_ ⊢ b' →
    -------------------------
    Γ ⊢ pi a b ⇒ Δ ⊢ pi a' b'
  | abs {Γ Δ b b'} :
    Γ ⇒ Δ →
    Γ ∷_ ⊢ b ⇒ Δ ∷_ ⊢ b' →
    ----------------------
    Γ ⊢ abs b ⇒ Δ ⊢ abs b'
  | app {Γ Δ b b' a a'} :
    Γ ⇒ Δ →
    Γ ⊢ b ⇒ Δ ⊢ b' →
    Γ ⊢ a ⇒ Δ ⊢ a' →
    ---------------------------
    Γ ⊢ app b a ⇒ Δ ⊢ app b' a'
  | letin {Γ Δ a a' b b'} :
    Γ ⇒ Δ →
    Γ ⊢ a ⇒ Δ ⊢ a' →
    Γ ∷_ ⊢ b ⇒ Δ ∷_ ⊢ b' →
    -------------------------------
    Γ ⊢ letin a b ⇒ Δ ⊢ letin a' b'
  | mty {Γ Δ} :
    Γ ⇒ Δ →
    -----------------
    Γ ⊢ mty ⇒ Δ ⊢ mty
  | exf {Γ Δ b b'} :
    Γ ⇒ Δ →
    Γ ⊢ b ⇒ Δ ⊢ b' →
    ----------------------
    Γ ⊢ exf b ⇒ Δ ⊢ exf b'
  | lvl {Γ Δ a a'} :
    Γ ⇒ Δ →
    Γ ⊢ a ⇒ Δ ⊢ a' →
    ----------------------
    Γ ⊢ lvl a ⇒ Δ ⊢ lvl a'
  | lof {Γ Δ} k :
    Γ ⇒ Δ →
    ---------------------
    Γ ⊢ lof k ⇒ Δ ⊢ lof k
end

notation:40 Γ:41 "⇒" Δ:41 => Par Γ Δ (Sigma.mk pe ())
notation:40 Γ:41 "⊢" a:41 "⇒" Δ:41 "⊢" b:41 => Par Γ Δ (Sigma.mk pt ⟨a, b⟩)

theorem parEnv {Γ Δ} (h : Γ ⇒ Δ) : Γ ∷_ ⇒ Δ ∷_ ∧ (∀ {a a'}, Γ ⊢ a ⇒ Δ ⊢ a' → Γ ∷ᵈ a ⇒ Δ ∷ᵈ a') := by
  generalize e : @Sigma.mk I idx I.pe () = t at h
  induction h
  all_goals injection e with eI; injection eI
  case nil => constructor; constructor; constructor; intro a a' r; constructor; constructor; assumption
  case cons ih _ =>
    let ⟨_, _⟩ := ih rfl
    constructor; constructor; assumption
    intro a a' r; constructor; assumption; assumption
  case dcons ih _ _ =>
    let ⟨_, _⟩ := ih rfl
    constructor; constructor; constructor; assumption; assumption
    intro a a' r; constructor; constructor; assumption; assumption; assumption

theorem parCons {Γ Δ} (h : Γ ⇒ Δ) : Γ ∷_ ⇒ Δ ∷_ := And.left (parEnv h)
theorem parDcons {Γ Δ a a'} (h : Γ ⇒ Δ) (ha : Γ ⊢ a ⇒ Δ ⊢ a') : Γ ∷ᵈ a ⇒ Δ ∷ᵈ a' := And.right (parEnv h) ha

theorem parConsTerm {Γ Δ a a'} (h : Γ ⇒ Δ) (ha : Γ ⊢ a ⇒ Δ ⊢ a') : Γ ∷_ ⊢ (rename succ a) ⇒ Δ ∷_ ⊢ (rename succ a') := by
  generalize e : @Sigma.mk I idx I.pt ⟨a, a'⟩ = t at ha
  induction ha generalizing a a'
  all_goals injection e with eI ea; injection eI
  all_goals injection ea with ea ea'; subst ea; subst ea'; simp only [rename] at *
  case β => sorry
  case ζ => sorry
  case δ => sorry
  all_goals constructor
  all_goals try constructor
  all_goals try assumption

theorem parEnvRefl {Γ a} : Γ ⇒ Γ ∧ Γ ⊢ a ⇒ Γ ⊢ a := by
  induction Γ generalizing a
  case nil =>
    induction a
    all_goals try rename _ ∧ _ => ih1; let ⟨ihe1, iht1⟩ := ih1; clear ih1
    all_goals try rename _ ∧ _ => ih2; let ⟨ihe2, iht2⟩ := ih2; clear ih2
    all_goals constructor
    all_goals constructor
    all_goals try constructor
    all_goals try assumption

theorem parRefl {Γ} a : Γ ⊢ a ⇒ a := by
  induction a generalizing Γ <;> constructor <;> apply_assumption

theorem parRename {Γ Δ a b} ξ (h : ξ ⊢ᵣ Γ ⟹ Δ) (r : Γ ⊢ a ⇒ b) : Δ ⊢ rename ξ a ⇒ rename ξ b := by
  induction r generalizing ξ Δ
  all_goals try rw [← renameDist]
  all_goals constructor
  all_goals try apply_rules [liftRenameAssn, liftRenameDefn]

theorem parLiftAssn {Γ} σ τ (h : ∀ x, Γ ⊢ σ x ⇒ τ x) : ∀ x, Γ ∷_ ⊢ (⇑ σ) x ⇒ (⇑ τ) x := by
  intro n; cases n
  case zero => constructor
  case succ n => apply_rules [parRename]; apply Is.athere

theorem parLiftDefn {Γ} σ τ (h : ∀ x, Γ ⊢ σ x ⇒ τ x) : ∀ x a, Γ ∷ᵈ a ⊢ (⇑ σ) x ⇒ (⇑ τ) x := by
  intro n a; cases n
  case zero => constructor
  case succ n => apply_rules [parRename]; intros _ _ _; apply_rules [Is.dthere]

theorem parMorphing {Γ Δ a b} σ τ (wτ : τ ⊢ₛ Γ ⟹ Δ) (h : ∀ x, Δ ⊢ σ x ⇒ τ x) (r : Γ ⊢ a ⇒ b) : Δ ⊢ subst σ a ⇒ subst τ b := by
  induction r generalizing σ τ Δ
  case δ xisa =>
    cases (wτ xisa)
    case inl e => rw [← e]; apply_assumption
    case inr h => let ⟨_, _, e⟩ := h; simp; sorry --rw [← wτ] <;> apply_assumption
  all_goals try rw [← substDist]
  all_goals try constructor
  all_goals try apply_rules [parLiftAssn, parLiftDefn, liftSubst]

theorem parSubst {Γ Δ a b} σ (wσ : σ ⊢ₛ Γ ⟹ Δ) (r : Γ ⊢ a ⇒ b) : Δ ⊢ subst σ a ⇒ subst σ b := by
  apply_rules [parMorphing]; intro; apply parRefl

theorem parCong {Γ a a' b b'} (ra : Γ ⊢ a ⇒ a') (rb : Γ ∷_ ⊢ b ⇒ b') : Γ ⊢ subst (a +: var) b ⇒ subst (a' +: var) b' := by
  apply parMorphing (r := rb)
  case h => intro n; cases n; assumption; constructor
  intro n; cases n
  case zero => intro _ zisa; cases zisa
  case succ => intro _ sisa; cases sisa; simp; sorry
  -- <;> first | assumption | constructor

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
