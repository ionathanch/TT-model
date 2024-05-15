import «TT-model».syntactics

open Term

set_option autoImplicit false

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
  | 𝒰 k : 𝒰 k ⇒ 𝒰 k
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
  | mty : Par mty mty
  | exf {b b'} :
    b ⇒ b' →
    --------------
    exf b ⇒ exf b'
end

infix:40 "⇒" => Par

theorem parRefl a : a ⇒ a := by
  induction a <;> constructor <;> assumption

theorem parRename {a b} ξ (r : a ⇒ b) : rename ξ a ⇒ rename ξ b := by
  revert ξ; induction r <;> intro ξ <;> try constructor
  case β ihb iha => rw [← renameDist]; constructor; apply ihb; apply iha
  case pi ih _ => apply ih
  case pi _ ih => apply ih
  case abs ih => apply ih
  case app ih _ => apply ih
  case app _ ih => apply ih
  case exf ih => apply ih

theorem parLift σ τ (h : ∀ x, σ x ⇒ τ x) : ∀ x, (⇑ σ) x ⇒ (⇑ τ) x := by
  intro n; cases n
  case zero => constructor
  case succ n => apply parRename; apply h

theorem parMorphing {a b} σ τ (h : ∀ x, σ x ⇒ τ x) (r : a ⇒ b) : subst σ a ⇒ subst τ b := by
  revert σ τ h; induction r <;> intro σ τ h <;> try constructor
  case β ihb iha =>
    rw [← substDist]; constructor
    . apply ihb; apply parLift; assumption
    . apply iha; assumption
  case var => apply h
  case pi ih _ => apply ih; assumption
  case pi _ ih => apply ih; apply parLift; assumption
  case abs ih => apply ih; apply parLift; assumption
  case app ih _ => apply ih; assumption
  case app _ ih => apply ih; assumption
  case exf ih => apply ih; assumption

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
  case trans ih => constructor; assumption; apply ih; assumption

theorem parsRename {a b} ξ (r : a ⇒⋆ b) : rename ξ a ⇒⋆ rename ξ b := by
  induction r
  case refl => constructor
  case trans ih => constructor; apply parRename; assumption; apply ih

theorem parsSubst {a b} σ (r : a ⇒⋆ b) : subst σ a ⇒⋆ subst σ b := by
  induction r
  case refl => constructor
  case trans ih => constructor; apply parSubst; assumption; apply ih

theorem parsCong {a a' b b'} (ra : a ⇒⋆ a') (rb : b ⇒⋆ b') : subst (a +: var) b ⇒⋆ subst (a' +: var) b' := by
  revert b b' rb; induction ra <;> intro b b' rb <;> induction rb
  case refl.refl => constructor
  case refl.trans =>
    constructor; apply parCong; apply parRefl; assumption; assumption
  case trans.refl ih _ =>
    constructor; apply parCong; assumption; apply parRefl; apply ih; constructor
  case trans.trans ih _ _ _ _ _ _ =>
    constructor; apply parCong; assumption; assumption; apply ih; assumption

/-*------------------------------------------
  Constructors for parallel multi-reduction
------------------------------------------*-/

theorem parsPi {a a' b b'} (ra : a ⇒⋆ a') (rb : b ⇒⋆ b') : pi a b ⇒⋆ pi a' b' := by
  revert b b' rb; induction ra <;> intro b b' rb <;> induction rb
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
  revert a a' ra; induction rb <;> intro a a' ra <;> induction ra
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

theorem parsβ σ b a : app (abs (subst (⇑ σ) b)) a ⇒⋆ subst (a +: σ) b := by
  constructor
  . constructor; apply parRefl; apply parRefl
  . rw [← substUnion]; constructor

/-*--------------------------------------------------
  Inversion principles for parallel multi-reduction
--------------------------------------------------*-/

theorem pars𝒰Inv {k b} (r : 𝒰 k ⇒⋆ b) : b = 𝒰 k := by
  generalize e : 𝒰 k = a at r
  induction r
  case refl => rfl
  case trans ra rb ih => subst e; cases ra; apply ih; rfl

theorem parsMtyInv {b} (r : mty ⇒⋆ b) : b = mty := by
  generalize e : mty = a at r
  induction r
  case refl => rfl
  case trans ra rb ih => subst e; cases ra; apply ih; rfl

theorem parsPiInv {a b c} (r : pi a b ⇒⋆ c) : ∃ a' b', c = pi a' b' ∧ a ⇒⋆ a' ∧ b ⇒⋆ b' := by
  generalize e : pi a b = c' at r
  revert a b e; induction r <;> intro a b e
  case refl => subst e; exact ⟨a, b, by simp; repeat constructor⟩
  case trans r _ ih =>
    subst e; cases r;
    match ih rfl with
    | ⟨a', b', e, _, _⟩ =>
      refine ⟨a', b', e, ?_, ?_⟩
      all_goals constructor <;> assumption

/-*---------------------------------------
  Confluence via Takahashi's translation
---------------------------------------*-/

@[simp]
def taka : Term → Term
  | pi a b => pi (taka a) (taka b)
  | abs b => abs (taka b)
  | app b a => match b with
    | abs b => subst (taka a +: var) (taka b)
    | b => app (taka b) (taka a)
  | exf b => exf (taka b)
  | t => t

theorem parTaka {a b} (r : a ⇒ b) : b ⇒ taka a := by
  induction r <;> try simp; (constructor <;> assumption)
  case β ihb iha => apply parCong <;> assumption
  case app b _ a _ r _ ih _ =>
    unfold taka; split
    . cases r; cases ih; apply Par.β <;> assumption
    . constructor <;> assumption

theorem diamond {a b c} (r₁ : a ⇒ b) (r₂ : a ⇒ c) : ∃ d, b ⇒ d ∧ c ⇒ d :=
  ⟨taka a, parTaka r₁, parTaka r₂⟩

/-*--------------------
      a
     / \
    b   d  by diamond
  // \ /
  c   e  by diacon
  \\ //
    f
--------------------*-/

theorem diacon {a b c} (r₁ : a ⇒⋆ b) (r₂ : a ⇒ c) : ∃ d, b ⇒⋆ d ∧ c ⇒⋆ d := by
  revert c; induction r₁ <;> intro d r
  case refl a => exact ⟨d, parPars r, refl d⟩
  case trans a b c r₁ _ ih =>
    match diamond r₁ r with
    | ⟨e, r₃, r₄⟩ =>
    match ih r₃ with
    | ⟨f, r₅, r₆⟩ => exact ⟨f, r₅, trans r₄ r₆⟩

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
  revert b r₁; induction r₂ <;> intro c r
  case refl b => exact ⟨c, refl c, r⟩
  case trans a b c r₁ _ ih =>
    match diacon r r₁ with
    | ⟨e, r₃, r₄⟩ =>
    match ih r₄ with
    | ⟨f, r₅, r₆⟩ => exact ⟨f, parsTrans r₃ r₅, r₆⟩

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

theorem convSym {a b} (r : a ⇔ b) : b ⇔ a :=
  match r with
  | ⟨c, ra, rb⟩ => ⟨c, rb, ra⟩

theorem convTrans {a b c} (r₁ : a ⇔ b) (r₂ : b ⇔ c) : a ⇔ c :=
  match r₁, r₂ with
  | ⟨_, rac, rbc⟩, ⟨_, rbd, rcd⟩ =>
  match confluence rbc rbd with
  | ⟨e, rce, rde⟩ =>
    ⟨e, parsTrans rac rce, parsTrans rcd rde⟩

theorem convSubst {a b} σ (r : a ⇔ b) : subst σ a ⇔ subst σ b :=
  match r with
  | ⟨c, ra, rb⟩ => ⟨subst σ c, parsSubst σ ra, parsSubst σ rb⟩

theorem convCong {a a' b b'} (ra : a ⇔ a') (rb : b ⇔ b') : subst (a +: var) b ⇔ subst (a' +: var) b' :=
  match ra, rb with
  | ⟨a'', ra, ra'⟩, ⟨b'', rb, rb'⟩ =>
    ⟨subst (a'' +: var) b'', parsCong ra rb, parsCong ra' rb'⟩

/-*----------------------------
  Constructors for conversion
----------------------------*-/

theorem convPi {a a' b b'} (ra : a ⇔ a') (rb : b ⇔ b') : pi a b ⇔ pi a' b' :=
  match ra, rb with
  | ⟨a'', ra, ra'⟩, ⟨b'', rb, rb'⟩ =>
    ⟨pi a'' b'', parsPi ra rb, parsPi ra' rb'⟩

theorem convAbs {b b'} (r : b ⇔ b') : abs b ⇔ abs b' :=
  match r with
  | ⟨b'', rb, rb'⟩ => ⟨abs b'', parsAbs rb, parsAbs rb'⟩

theorem convApp {b b' a a'} (rb : b ⇔ b') (ra : a ⇔ a') : app b a ⇔ app b' a' :=
  match rb, ra with
  | ⟨b'', rb, rb'⟩, ⟨a'', ra, ra'⟩ =>
    ⟨app b'' a'', parsApp rb ra, parsApp rb' ra'⟩

theorem convExf {b b'} (r : b ⇔ b') : exf b ⇔ exf b' :=
  match r with
  | ⟨b'', rb, rb'⟩ => ⟨exf b'', parsExf rb, parsExf rb'⟩

/-*------------------------------------
  Inversion principles for conversion
------------------------------------*-/

theorem conv𝒰Mty {k} : ¬ 𝒰 k ⇔ mty
  | ⟨_, r𝒰, rmty⟩ => by
    have e𝒰 := pars𝒰Inv r𝒰
    have emty := parsMtyInv rmty
    subst emty; contradiction

theorem conv𝒰Pi {k a b} : ¬ 𝒰 k ⇔ pi a b
  | ⟨_, r𝒰, rpi⟩ => by
    have e𝒰 := pars𝒰Inv r𝒰
    match parsPiInv rpi with
    | ⟨_, _, epi, _, _⟩ => subst epi; contradiction

theorem convMtyPi {a b} : ¬ mty ⇔ pi a b
  | ⟨_, rmty, rpi⟩ => by
    have emty := parsMtyInv rmty
    match parsPiInv rpi with
    | ⟨_, _, epi, _, _⟩ => subst epi; contradiction

theorem conv𝒰Inv {j k} : 𝒰 j ⇔ 𝒰 k → j = k
  | ⟨_, rj, rk⟩ => by
    have ej := pars𝒰Inv rj
    have ek := pars𝒰Inv rk
    subst ej; injection ek

theorem convPiInv {a₁ a₂ b₁ b₂} : pi a₁ b₁ ⇔ pi a₂ b₂ → a₁ ⇔ a₂ ∧ b₁ ⇔ b₂
  | ⟨_, r₁, r₂⟩ =>
  match parsPiInv r₁, parsPiInv r₂ with
  | ⟨a₁', b₁', e₁, ra₁, rb₁⟩, ⟨a₂', b₂', e₂, ra₂, rb₂⟩ => by
    subst e₁; injection e₂ with ea eb
    subst ea; subst eb
    exact ⟨⟨a₁', ra₁, ra₂⟩, ⟨b₁', rb₁, rb₂⟩⟩
