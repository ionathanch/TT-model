import «TT-model».level

open Nat

set_option autoImplicit false
set_option pp.fieldNotation false

variable [lc : LevelClass]

@[simp]
def cons {A : Type} (x : A) (ξ : Nat → A) : Nat → A
  | 0 => x
  | n + 1 => ξ n
infixr:50 "+:" => cons

/-*------
  Terms
------*-/

inductive Term : Type where
  | var : Nat → Term
  | 𝒰 : Term → Term
  | pi : Term → Term → Term
  | abs : Term → Term
  | app : Term → Term → Term
  | letin : Term → Term → Term
  | mty : Term
  | exf : Term → Term
  | lvl : Term → Term
  | lof : lc.L → Term
open Term

/-*------------------
  Lifting renamings
------------------*-/

@[simp]
def lift (ξ : Nat → Nat) : Nat → Nat :=
  zero +: (succ ∘ ξ)

-- Lifting composes
theorem liftComp ξ ζ ς (h : ∀ x, (ξ ∘ ζ) x = ς x) :
  ∀ x, (lift ξ ∘ lift ζ) x = lift ς x := by
  intro x; cases x <;> simp
  case succ => apply h

/-*-------------------
  Applying renamings
-------------------*-/

@[simp]
def rename (ξ : Nat → Nat) : Term → Term
  | var s => var (ξ s)
  | 𝒰 a => 𝒰 (rename ξ a)
  | pi a b => pi (rename ξ a) (rename (lift ξ) b)
  | abs b => abs (rename (lift ξ) b)
  | app b a => app (rename ξ b) (rename ξ a)
  | letin a b => letin (rename ξ a) (rename (lift ξ) b)
  | mty => mty
  | exf b => exf (rename ξ b)
  | lvl a => lvl (rename ξ a)
  | lof k => lof k

-- Renaming compositionality
theorem renameComp' ξ ζ ς (h : ∀ x, (ξ ∘ ζ) x = ς x) : ∀ s, (rename ξ ∘ rename ζ) s = rename ς s := by
  intro s; induction s generalizing ξ ζ ς
  all_goals simp; try constructor
  all_goals apply_rules [liftComp]

-- Renaming compositionality, extensionally
theorem renameComp ξ ζ s : (rename ξ ∘ rename ζ) s = rename (ξ ∘ ζ) s := by
  apply renameComp'; simp

-- Lifting respects renaming extensionality
theorem liftExt ξ ζ (h : ∀ x, ξ x = ζ x) : ∀ x, (lift ξ) x = (lift ζ) x := by
  intro n; cases n <;> simp [h]

-- Renaming extensionality
theorem renameExt ξ ζ (h : ∀ x, ξ x = ζ x) : ∀ s, rename ξ s = rename ζ s := by
  intro s; induction s generalizing ξ ζ
  all_goals simp; try constructor
  all_goals apply_rules [liftExt]

-- Lift commutes with shifting beneath renaming
theorem renameLiftShift ξ s : (rename (lift ξ) ∘ rename succ) s = (rename succ ∘ rename ξ) s := by
  rw [renameComp (lift ξ) succ, renameComp succ ξ]
  apply_rules [renameExt]

theorem renameLiftShifted ξ s : rename (lift ξ) (rename succ s) = rename succ (rename ξ s) := by
  apply renameLiftShift

theorem renameLift ξ a s : (rename ξ ∘ (a +: var)) s = ((rename ξ a +: var) ∘ lift ξ) s := by
  cases s <;> rfl

/-*----------------------
  Lifting substitutions
----------------------*-/

@[simp]
def up (σ : Nat → Term) : Nat → Term :=
  var 0 +: (rename succ ∘ σ)
prefix:95 "⇑" => up

-- Lifting twice pushes renamings inwards
theorem upUp σ x : (⇑ ⇑ σ) x = (var 0 +: var 1 +: (rename succ ∘ rename succ ∘ σ)) x := by
  cases x; rfl
  case succ n => cases n <;> rfl

-- Lifting var "substitution" does nothing
theorem upId σ (h : ∀ x, σ x = var x) : ∀ x, (⇑ σ) x = var x := by
  intro n; cases n <;> simp [h]

-- Lifting respects subsitution extensionality
theorem upExt σ τ (h : ∀ x, σ x = τ x) : ∀ x, (⇑ σ) x = (⇑ τ) x := by
  intro n; cases n <;> simp [h]

-- Lifting commutes with composition
theorem upLift ξ σ τ (h : ∀ x, (σ ∘ ξ) x = τ x) : ∀ x, (⇑ σ ∘ lift ξ) x = (⇑ τ) x := by
  intro n; cases n <;> simp [← h]

-- Lifting commutes with renaming
theorem upRename ξ σ τ (h : ∀ x, (rename ξ ∘ σ) x = τ x) : ∀ x, (rename (lift ξ) ∘ ⇑ σ) x = (⇑ τ) x := by
  intro n; cases n; simp
  case succ n => calc
    (rename (lift ξ) ∘ rename succ) (σ n)
      = rename (lift ξ ∘ succ) (σ n)      := by rw [renameComp]
    _ = (rename (succ ∘ ξ)) (σ n)         := by simp [Function.comp]
    _ = (rename succ ∘ rename ξ) (σ n)    := by rw [renameComp]
    _ = (rename succ (rename ξ (σ n)))    := by rfl
    _ = rename succ (τ n)                 := by simp [← h]

/-*-----------------------
  Applying substitutions
-----------------------*-/

@[simp]
def subst (σ : Nat → Term) : Term → Term
  | var s => σ s
  | 𝒰 a => 𝒰 (subst σ a)
  | pi a b => pi (subst σ a) (subst (⇑ σ) b)
  | abs b => abs (subst (⇑ σ) b)
  | app b a => app (subst σ b) (subst σ a)
  | letin a b => letin (subst σ a) (subst (⇑ σ) b)
  | mty => mty
  | exf b => exf (subst σ b)
  | lvl a => lvl (subst σ a)
  | lof k => lof k

-- Substitution extensionality
theorem substExt σ τ (h : ∀ x, σ x = τ x) : ∀ s, subst σ s = subst τ s := by
  intro s; induction s generalizing σ τ
  all_goals simp; try constructor
  all_goals apply_rules [upExt]

-- Applying var "substitution" does nothing
theorem substId' σ (h : ∀ x, σ x = var x) : ∀ s, subst σ s = s := by
  intro s; induction s generalizing σ
  all_goals simp; try constructor
  all_goals apply_rules [upId]

-- Substitution/renaming compositionality
theorem substRename' ξ σ τ (h : ∀ x, (σ ∘ ξ) x = τ x) : ∀ s, subst σ (rename ξ s) = subst τ s := by
  intro s; induction s generalizing ξ σ τ
  all_goals simp; try constructor
  all_goals apply_rules [upLift]

-- Renaming/substitution compositionality
theorem renameSubst' ξ σ τ (h : ∀ x, (rename ξ ∘ σ) x = τ x) : ∀ s, rename ξ (subst σ s) = subst τ s := by
  intro s; induction s generalizing ξ σ τ
  all_goals simp; try constructor
  all_goals apply_rules [upRename]

-- Lifting commutes with substitution
theorem upSubst ρ σ τ (h : ∀ x, (subst ρ ∘ σ) x = τ x) : ∀ x, (subst (⇑ ρ) ∘ (⇑ σ)) x = (⇑ τ) x := by
  intro n; cases n; rfl
  case succ n => calc
    (subst (⇑ ρ) ∘ rename succ) (σ n)
      = subst (⇑ ρ ∘ succ) (σ n)      := by rw [← substRename']; rfl; simp
    _ = subst (rename succ ∘ ρ) (σ n) := by rfl
    _ = (rename succ ∘ subst ρ) (σ n) := by rw [← renameSubst']; rfl; simp
    _ = rename succ (subst ρ (σ n))   := by rfl
    _ = rename succ (τ n)             := by simp [← h]

-- Substitution compositionality
theorem substComp' ρ σ τ (h : ∀ x, (subst ρ ∘ σ) x = τ x) : ∀ s, (subst ρ ∘ subst σ) s = subst τ s := by
  intro s; induction s generalizing ρ σ τ
  all_goals simp; try constructor
  all_goals apply_rules [upSubst]

/-*----------------------------------------------
  Substitution & renaming lemmas, extensionally
----------------------------------------------*-/

def substId : ∀ s, subst var s = s :=
  substId' var (by simp)

def substRename ξ σ : ∀ s, (subst σ ∘ (rename ξ)) s = subst (σ ∘ ξ) s :=
  substRename' _ _ (σ ∘ ξ) (by simp)

def substRenamed ξ σ : ∀ s, subst σ (rename ξ s) = subst (σ ∘ ξ) s :=
  substRename' _ _ (σ ∘ ξ) (by simp)

def renameSubst ξ σ : ∀ s, (rename ξ ∘ subst σ) s = subst (rename ξ ∘ σ) s :=
  renameSubst' _ _ (rename ξ ∘ σ) (by simp)

def substComp σ τ : ∀ s, (subst σ ∘ subst τ) s = subst (subst σ ∘ τ) s :=
  substComp' _ _ (subst σ ∘ τ) (by simp)

/-*-------------------------------------------------
  Handy dandy derived renaming substitution lemmas
-------------------------------------------------*-/

-- Lifting commutes with shifting below substitution
theorem substLiftShift σ s : (rename succ ∘ subst σ) s = (subst (⇑ σ) ∘ rename succ) s := by
  rw [substRename, renameSubst]
  apply_rules [substExt]

theorem substLiftShifted σ s : rename succ (subst σ s) = subst (⇑ σ) (rename succ s) := by
  apply substLiftShift

theorem renameDist ξ a s : subst (rename ξ a +: var) (rename (lift ξ) s) = rename ξ (subst (a +: var) s) := by
  calc
    subst (rename ξ a +: var) (rename (lift ξ) s)
      = (subst (rename ξ a +: var) ∘ rename (lift ξ)) s := by rfl
    _ = subst ((rename ξ a +: var) ∘ lift ξ) s          := by rw [substRename]
    _ = subst (rename ξ ∘ (a +: var)) s                 := by apply substExt; intros; rw [renameLift]
    _ = rename ξ (subst (a +: var) s)                   := by simp [← renameSubst]

theorem substDrop a b : b = subst (a +: var) (rename succ b) := by
  calc
    b = subst var b                          := by rw [substId]
    _ = (subst (a +: var) ∘ (rename succ)) b := by rw [substRename]; rfl

theorem substUnion σ a s : subst (a +: σ) s = subst (a +: var) (subst (⇑ σ) s) := by
  calc
    subst (a +: σ) s
      = subst (subst (a +: var) ∘ (var 0 +: (rename succ ∘ σ))) s :=
        by apply substExt; intro n; cases n <;> simp [← substDrop]
    _ = subst (a +: var) (subst (⇑ σ) s) :=
        by simp [← substComp]

theorem substDist σ a s : subst (subst σ a +: var) (subst (⇑ σ) s) = subst σ (subst (a +: var) s) := by
  calc
    subst (subst σ a +: var) (subst (⇑ σ) s)
      = subst (subst σ a +: σ) s       := by rw [← substUnion]
    _ = subst (subst σ ∘ (a +: var)) s := by apply substExt; intro n; cases n <;> rfl
    _ = (subst σ ∘ subst (a +: var)) s := by rw [← substComp]

/-*------------------------
  Contexts and membership
------------------------*-/

inductive Ctxt : Type where
  | nil : Ctxt
  | cons : Ctxt → Term → Ctxt
  | dcons : Ctxt → Term → Term → Ctxt
notation:50 "⬝" => Ctxt.nil
infixl:50 "∷" => Ctxt.cons
notation:50 Γ:51 "∷ᵈ" a:51 "≔" A:51 => Ctxt.dcons Γ a A

inductive In : Nat → Term → Ctxt → Prop where
  | ahere {Γ A} : In 0 (rename succ A) (Γ ∷ A)
  | dhere {Γ a A} : In 0 (rename succ A) (Γ ∷ᵈ a ≔ A)
  | athere {Γ x A B} : In x B Γ → In (succ x) (rename succ B) (Γ ∷ A)
  | dthere {Γ x a A B} : In x B Γ → In (succ x) (rename succ B) (Γ ∷ᵈ a ≔ A)
notation:40 Γ:41 "∋" x:41 "∶" A:41 => In x A Γ

-- Handy membership helper constructors

theorem inAHere {Γ A A'} (e : rename succ A = A') : (Γ ∷ A) ∋ 0 ∶ A' := by
  subst e; constructor

theorem inDHere {Γ a A A'} (e : rename succ A = A') : (Γ ∷ᵈ a ≔ A) ∋ 0 ∶ A' := by
  subst e; constructor

theorem inThere {Γ x A A' B} (h : Γ ∋ x ∶ A) (e : A' = rename succ A) : Γ ∷ B ∋ succ x ∶ A' := by
  subst e; constructor; assumption

/-*-----------------------------
  Environments and membership
  (contexts stripped of types)
-----------------------------*-/

inductive Env : Type where
  | nil : Env
  | cons : Env → Env
  | dcons : Env → Term → Env
notation:50 "⬝" => Env.nil
postfix:50 "∷_" => Env.cons
notation:50 Γ:51 "∷ᵈ" a:51 => Env.dcons Γ a

def untype (Γ : Ctxt) : Env :=
  match Γ with
  | ⬝ => ⬝
  | Γ ∷ _ => untype Γ ∷_
  | Γ ∷ᵈ a ≔ _ => untype Γ ∷ᵈ a
notation:30 "|" Γ:31 "|" => untype Γ

inductive Is : Nat → Term → Env → Prop where
  | here {Γ a} : Is 0 (rename succ a) (Γ ∷ᵈ a)
  | athere {Γ x a} : Is x a Γ → Is (succ x) (rename succ a) (Γ ∷_)
  | dthere {Γ x a b} : Is x a Γ → Is (succ x) (rename succ a) (Γ ∷ᵈ b)
  notation:40 Γ:41 "∋" x:41 "≔" a:41 => Is x a Γ

-- Handy membership helper constructors

theorem isHere {Γ a a'} (e : a' = rename succ a) : (Γ ∷ᵈ a) ∋ 0 ≔ a' := by
  subst e; constructor

theorem isAThere {Γ x a a'} (h : Γ ∋ x ≔ a) (e : rename succ a = a') : Γ ∷_ ∋ succ x ≔ a' := by
  subst e; constructor; assumption

theorem isDThere {Γ x a a' b} (h : Γ ∋ x ≔ a) (e : rename succ a = a') : Γ ∷ᵈ b ∋ succ x ≔ a' := by
  subst e; constructor; assumption

/-*---------------------------------------
  Well-defined renamings with respect to
  source and target environments
---------------------------------------*-/

def Wdr ξ Γ Δ := ∀ {x a}, Γ ∋ x ≔ a → Δ ∋ ξ x ≔ rename ξ a
notation:40 ξ:41 "⊢ᵣ" Γ:41 "⟹" Δ:41 => Wdr ξ Γ Δ

theorem liftRenameAssn {ξ Γ Δ} (h : ξ ⊢ᵣ Γ ⟹ Δ) : lift ξ ⊢ᵣ Γ ∷_ ⟹ Δ ∷_ := by
  intro _ _ xisa; cases xisa; rw [renameLiftShifted]; apply_rules [isAThere, renameLiftShift]

theorem liftRenameDefn {ξ Γ Δ} a (h : ξ ⊢ᵣ Γ ⟹ Δ) : lift ξ ⊢ᵣ Γ ∷ᵈ a ⟹ Δ ∷ᵈ (rename ξ a) := by
  intro _ _ xisa; cases xisa; all_goals rw [renameLiftShifted]; apply_rules [isHere, isDThere]

def Wds (σ : Nat → Term) Γ Δ := ∀ {x a}, Γ ∋ x ≔ a →
  (σ x = subst σ a) ∨
  (∃ y, Δ ∋ y ≔ subst σ a ∧ σ x = var y)
notation:40 σ:41 "⊢ₛ" Γ:41 "⟹" Δ:41 => Wds σ Γ Δ

theorem liftSubst {σ : Nat → Term} {Γ Δ} (h : σ ⊢ₛ Γ ⟹ Δ) : ⇑ σ ⊢ₛ Γ ∷_ ⟹ Δ ∷_ := by
  intro _ _ xisa; cases xisa with | athere xisa =>
    cases (h xisa)
    case inl e => simp [e, substLiftShifted]
    case inr h =>
      let ⟨_, yisa, e⟩ := h
      exact Or.inr ⟨_, by apply_rules [isAThere, substLiftShifted], by simp [e]⟩

theorem varSubst {Γ} : var ⊢ₛ Γ ⟹ Γ := by
  cases Γ
  all_goals intro _ _ xisa; rw [substId]; cases xisa
  all_goals refine Or.inr ⟨_, by apply_rules [isHere, isAThere, isDThere], rfl⟩
