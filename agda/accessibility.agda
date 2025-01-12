{-# OPTIONS --rewriting --confluence-check #-}

open import common

{-# BUILTIN REWRITE _≡_ #-}

module accessibility
  (Level : Set)
  (_<_ : Level → Level → Set) where

record Acc (k : Level) : Set where
  pattern
  inductive
  constructor acc<
  field acc : ∀ {j} → j < k → Acc j
open Acc

module ext where
  private postulate
    funext' : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} →
      {f g : ∀ {x} → B x} → (∀ x → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ (λ {x} → g {x})
    funext : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} →
      {f g : ∀ x → B x} → (∀ x → f x ≡ g x) → f ≡ g

  funext-β : ∀ {ℓ ℓ' A B f} → funext {f = f} (λ _ → refl) ≡ refl
  funext-β {ℓ} {ℓ'} {A} {B} {f} with refl ← funext {ℓ} {ℓ'} {A} {B} {f} (λ _ → refl) = refl

  {-# REWRITE funext-β #-}

  piext : ∀ {A A'} {B : A → Set} {B' : A' → Set} →
          (p : A ≡ A') → (∀ x → B x ≡ B' (coe p x)) → (∀ x → B x) ≡ (∀ x → B' x)
  piext refl h = cong (λ B → ∀ x → B x) (funext h)

  accProp : ∀ {k} (p q : Acc k) → p ≡ q
  accProp (acc< f) (acc< g) = cong acc< (funext' (λ j → funext (λ j<k → accProp (f j<k) (g j<k))))