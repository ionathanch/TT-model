open import Agda.Builtin.Unit using (⊤ ; tt) public
open import Agda.Builtin.Nat using (Nat ; zero ; suc) public
open import Function.Base using (_∘_) public
open import Data.Empty using (⊥) public
open import Data.Product.Base using (Σ-syntax ; ∃-syntax ; _×_ ; _,_) public
open import Relation.Binary.PropositionalEquality public
  using (_≡_ ; refl ; sym ; trans ; cong ; module ≡-Reasoning)
  renaming (subst to transp)
open ≡-Reasoning public

coe : ∀ {A B : Set} → A ≡ B → A → B
coe refl x = x