open import common

module accessibility
  (Level : Set)
  (_<_ : Level → Level → Set) where

record Acc (k : Level) : Set where
  pattern
  inductive
  constructor acc<
  field acc : ∀ {j} → j < k → Acc j
open Acc

module accext where
  private postulate
    funext' : ∀ {A : Set} {B : A → Set} →
      {f g : ∀ {x} → B x} → (∀ x → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ (λ {x} → g {x})
    funext : ∀ {A : Set} {B : A → Set} →
      {f g : ∀ x → B x} → (∀ x → f x ≡ g x) → f ≡ g

  accProp : ∀ {k} (p q : Acc k) → p ≡ q
  accProp (acc< f) (acc< g) = cong acc< (funext' (λ j → funext (λ j<k → accProp (f j<k) (g j<k))))