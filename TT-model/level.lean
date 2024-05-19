import Mathlib.Order.RelClasses

/-*----------------------------------------------------------
  Typeclass for levels and their required properties:
  * Wellfoundedness is needed to build the logical relation
  * Transitivity is needed for cumulativity of the LR
  * Trichotomy is needed for determinism of the LR
  * Lsucc is needed since every type has a type
----------------------------------------------------------*-/

class LevelClass where
  L : Type
  lt : L → L → Prop
  wo : IsWellOrder L lt
  lsucc i : ∃ j, lt i j
open LevelClass

infix:50 "<" => lt

attribute [instance] wo

instance [LevelClass] : WellFoundedRelation L :=
  wo.toWellFoundedRelation

/-*---------------------------------
  The naturals are suitable levels
---------------------------------*-/

@[simp]
instance LNat : LevelClass where
  L := Nat
  lt := LT.lt
  wo := Nat.lt.isWellOrder
  lsucc := λ i ↦ ⟨Nat.succ i, by omega⟩

instance LOfNat : OfNat L n where
  ofNat := n
