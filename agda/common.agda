open import Agda.Builtin.Unit using (⊤ ; tt) public
open import Agda.Builtin.Nat using (Nat ; zero ; suc) public
open import Function.Base using (id ; _∘_) public
open import Data.Empty using (⊥) public
open import Data.Product.Base using (Σ-syntax ; ∃-syntax ; _×_ ; _,_) public
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′) public
open import Relation.Binary.PropositionalEquality public
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; module ≡-Reasoning)
  renaming (subst to transp ; subst₂ to transp₂)
open ≡-Reasoning public

_↔_ : Set → Set → Set
A ↔ B = (A → B) × (B → A)

coe : ∀ {A B : Set} → A ≡ B → A → B
coe refl x = x

coe-β : ∀ {A B : Set} (p : A ≡ B) x → coe (sym p) (coe p x) ≡ x
coe-β refl x = refl