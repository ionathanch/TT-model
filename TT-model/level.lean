import Mathlib.Order.RelClasses
import Mathlib.Order.Max

set_option autoImplicit false
set_option pp.fieldNotation false

/-*----------------------------------------------------------
  Typeclass for levels and their required properties:
  * Wellfoundedness is needed to build the logical relation
  * Transitivity is needed for cumulativity of the LR
  * Trichotomy is needed for determinism of the LR
  * Cofinality is needed since every type has a type
----------------------------------------------------------*-/

class LevelClass where
  L : Type
  lt : LT L
  wo : IsWellOrder L lt.lt
  cf : NoMaxOrder L
open LevelClass

attribute [instance] lt
attribute [instance] wo
attribute [instance] cf

instance [LevelClass] : WellFoundedRelation L :=
  wo.toWellFoundedRelation

/-*---------------------------------
  The naturals are suitable levels
---------------------------------*-/

instance instNoMaxOrderNat : NoMaxOrder Nat where
  exists_gt := λ i ↦ ⟨Nat.succ i, by omega⟩

@[simp]
instance : LevelClass where
  L := Nat
  lt := instLTNat
  wo := Nat.lt.isWellOrder
  cf := instNoMaxOrderNat

instance (n : Nat) : OfNat L n where
  ofNat := n
