import «TT-model».level

open Nat

set_option autoImplicit false

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
  | mty => mty
  | exf b => exf (rename ξ b)
  | lvl a => lvl (rename ξ a)
  | lof k => lof k

-- Renamings compose
theorem renameComp' ξ ζ ς (h : ∀ x, (ξ ∘ ζ) x = ς x) : ∀ s, (rename ξ ∘ rename ζ) s = rename ς s := by
  intro s; revert ξ ζ ς h; induction s
  all_goals intro ξ ζ ς h; simp; try constructor
  case var s => simp [← h]
  case 𝒰 ih => apply ih; assumption
  case pi.left ih _ => apply ih; assumption
  case pi.right _ ih => apply ih; apply liftComp; assumption
  case abs ih => apply ih; apply liftComp; assumption
  case app ih _ => apply ih; assumption
  case app _ ih => apply ih; assumption
  case exf ih => apply ih; assumption
  case lvl ih => apply ih; assumption

theorem renameComp ξ ζ s : (rename ξ ∘ rename ζ) s = rename (ξ ∘ ζ) s := by
  apply renameComp'; simp

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
    _ = (rename (succ ∘ ξ)) (σ n)         := by unfold Function.comp; rfl
    _ = (rename succ ∘ rename ξ) (σ n)    := by rw [renameComp]
    _ = (rename succ (rename ξ (σ n)))    := by rfl
    _ = rename succ (τ n)                 := by rw [← h]; rfl

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
  | mty => mty
  | exf b => exf (subst σ b)
  | lvl a => lvl (subst σ a)
  | lof k => lof k

-- Substitution extensionality
theorem substExt σ τ (h : ∀ x, σ x = τ x) : ∀ s, subst σ s = subst τ s := by
  intro s; revert σ τ h; induction s
  all_goals intro σ τ h; simp; try constructor
  case var => rw [h]
  case 𝒰 ih => apply ih; assumption
  case pi.left ih _ => apply ih; assumption
  case pi.right _ ih => apply ih; apply upExt; assumption
  case abs ih => apply ih; apply upExt; assumption
  case app.left ih _ => apply ih; assumption
  case app.right _ ih => apply ih; assumption
  case exf ih => apply ih; assumption
  case lvl ih => apply ih; assumption

-- Applying var "substitution" does nothing
theorem substId' σ (h : ∀ x, σ x = var x) : ∀ s, subst σ s = s := by
  intro s; revert σ h; induction s
  all_goals intro σ h; simp; try constructor
  case var => rw [h]
  case 𝒰 ih => apply ih; assumption
  case pi.left ih _ => apply ih; assumption
  case pi.right _ ih => apply ih; apply upId; assumption
  case abs ih => apply ih; apply upId; assumption
  case app.left ih _ => apply ih; assumption
  case app.right _ ih => apply ih; assumption
  case exf ih => apply ih; assumption
  case lvl ih => apply ih; assumption

-- Substitution/renaming compositionality
theorem substRename' ξ σ τ (h : ∀ x, (σ ∘ ξ) x = τ x) : ∀ s, subst σ (rename ξ s) = subst τ s := by
  intro s; revert ξ σ τ h; induction s
  all_goals intro ξ σ τ h; simp; try constructor
  case var => simp [← h]
  case 𝒰 ih => apply ih; assumption
  case pi.left ih _ => apply ih; assumption
  case pi.right _ ih => apply ih; apply upLift; assumption
  case abs ih => apply ih; apply upLift; assumption
  case app.left ih _ => apply ih; assumption
  case app.right _ ih => apply ih; assumption
  case exf ih => apply ih; assumption
  case lvl ih => apply ih; assumption

-- Renaming/substitution compositionality
theorem renameSubst' ξ σ τ (h : ∀ x, (rename ξ ∘ σ) x = τ x) : ∀ s, rename ξ (subst σ s) = subst τ s := by
  intro s; revert ξ σ τ h; induction s
  all_goals intro ξ σ τ h; simp; try constructor
  case var => simp [← h]
  case 𝒰 ih => apply ih; assumption
  case pi.left ih _ => apply ih; assumption
  case pi.right _ ih => apply ih; apply upRename; assumption
  case abs ih => apply ih; apply upRename; assumption
  case app.left ih _ => apply ih; assumption
  case app.right _ ih => apply ih; assumption
  case exf ih => apply ih; assumption
  case lvl ih => apply ih; assumption

-- Lifting commutes with substitution
theorem upSubst ρ σ τ (h : ∀ x, (subst ρ ∘ σ) x = τ x) : ∀ x, (subst (⇑ ρ) ∘ (⇑ σ)) x = (⇑ τ) x := by
  intro n; cases n; rfl
  case succ n => calc
    (subst (⇑ ρ) ∘ rename succ) (σ n)
      = subst (⇑ ρ ∘ succ) (σ n)      := by rw [← substRename']; rfl; simp
    _ = subst (rename succ ∘ ρ) (σ n) := by rfl
    _ = (rename succ ∘ subst ρ) (σ n) := by rw [← renameSubst']; rfl; simp
    _ = rename succ (subst ρ (σ n))   := by rfl
    _ = rename succ (τ n)             := by rw [← h]; rfl

-- Substitution compositionality
theorem substComp' ρ σ τ (h : ∀ x, (subst ρ ∘ σ) x = τ x) : ∀ s, (subst ρ ∘ subst σ) s = subst τ s := by
  intro s; revert ρ σ τ h; induction s
  all_goals intro ξ σ τ h; simp; try constructor
  case var => simp [← h]
  case 𝒰 ih => apply ih; assumption
  case pi.left ih _ => apply ih; assumption
  case pi.right _ ih => apply ih; apply upSubst; assumption
  case abs ih => apply ih; apply upSubst; assumption
  case app.left ih _ => apply ih; assumption
  case app.right _ ih => apply ih; assumption
  case exf ih => apply ih; assumption
  case lvl ih => apply ih; assumption

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

theorem renameDist ξ a s : subst (rename ξ a +: var) (rename (lift ξ) s) = rename ξ (subst (a +: var) s) := by
  calc
    subst (rename ξ a +: var) (rename (lift ξ) s)
      = (subst (rename ξ a +: var) ∘ rename (lift ξ)) s := by rfl
    _ = subst ((rename ξ a +: var) ∘ lift ξ) s          := by rw [substRename]
    _ = subst (rename ξ ∘ (a +: var)) s                 := by apply substExt; intros; rw [renameLift]
    _ = rename ξ (subst (a +: var) s)                   := by rw [← renameSubst]; rfl

theorem substDrop a b : b = subst (a +: var) (rename succ b) := by
  calc
    b = subst var b                          := by rw [substId]
    _ = (subst (a +: var) ∘ (rename succ)) b := by rw [substRename]; rfl

theorem substUnion σ a s : subst (a +: σ) s = subst (a +: var) (subst (⇑ σ) s) := by
  calc
    subst (a +: σ) s
      = subst (subst (a +: var) ∘ (var 0 +: (rename succ ∘ σ))) s :=
        by apply substExt; intro n; cases n <;> simp; rw [← substDrop]
    _ = subst (a +: var) (subst (⇑ σ) s) :=
        by rw [← substComp]; rfl

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
notation:50 "⬝" => Ctxt.nil
infixl:50 "∷" => Ctxt.cons

inductive In : Nat → Term → Ctxt → Prop where
  | here {Γ A} : In 0 (rename succ A) (Γ ∷ A)
  | there {Γ x A B} : In x A Γ → In (succ x) (rename succ A) (Γ ∷ B)
notation:40 Γ:41 "∋" x:41 "∶" A:41 => In x A Γ

theorem inHere {Γ A A'} (e : A' = rename succ A) : (Γ ∷ A) ∋ 0 ∶ A' := by
  subst e; apply In.here

theorem inThere {Γ x A A' B} (h : Γ ∋ x ∶ A) (e : A' = rename succ A) : Γ ∷ B ∋ succ x ∶ A' := by
  subst e; apply In.there; assumption
