open import Agda.Builtin.Unit using (⊤ ; tt) public
open import Agda.Builtin.Nat using (Nat ; zero ; suc) public
open import Function.Base using (id ; _∘_) public
open import Data.Empty using (⊥) public
open import Data.Product.Base using (Σ-syntax ; ∃-syntax ; _×_ ; _,_) public
open import Relation.Binary.PropositionalEquality public
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; module ≡-Reasoning)
  renaming (subst to transp)
open ≡-Reasoning public

_↔_ : Set → Set → Set
A ↔ B = Σ[ f ∈ (A → B) ] Σ[ g ∈ (B → A) ] (∀ x → f (g x) ≡ x) × (∀ x → g (f x) ≡ x)

coe : ∀ {A B : Set} → A ≡ B → A → B
coe refl x = x

coe-β : ∀ {A B : Set} (p : A ≡ B) x → coe (sym p) (coe p x) ≡ x
coe-β refl x = refl

congd : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A}
        (f : (z : A) → x ≡ z → B) (p : x ≡ y) → f x refl ≡ f y p
congd f refl = refl

transpK : ∀ {ℓ ℓ'} {A : Set ℓ} {x : A} (P : A → Set ℓ') (p : x ≡ x) d → transp P p d ≡ d
transpK P refl d = refl