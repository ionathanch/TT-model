open import common
import syntactics
import reduction

module typing
  (Level : Set)
  (_<_ : Level → Level → Set)
  (trans< : ∀ {i j k} → i < j → j < k → i < k) where
open syntactics Level
open reduction Level

data _≤_ : Level → Level → Set where
  eq : ∀ {k} → k ≤ k
  lt : ∀ {j k} → j < k → j ≤ k

{------------------------
  Definitional equality
------------------------}

data _≈_ : Term → Term → Set where
  ≈-refl  : ∀ {a} → a ≈ a
  ≈-sym   : ∀ {a b} →
            b ≈ a →
            ---------
            a ≈ b
  ≈-trans : ∀ {a b c} →
            a ≈ b →
            b ≈ c →
            -----------
            a ≈ c
  ≈-β     : ∀ {b a} →
            --------------------------------
            $ᵈ (λᵈ b) a ≈ subst (a +: var) b
  ≈-Π     : ∀ {a a' j b b'} →
            a ≈ a' →
            b ≈ b' →
            -------------------
            Π a j b ≈ Π a' j b'
  ≈-λᵈ    : ∀ {b b'} →
            b ≈ b' →
            ------------
            λᵈ b ≈ λᵈ b'
  ≈-$ᵈ    : ∀ {b b' a a'} →
            b ≈ b' →
            a ≈ a' →
            -----------------
            $ᵈ b a ≈ $ᵈ b' a'
  ≈-abs   : ∀ {b b'} →
            b ≈ b' →
            --------------
            abs b ≈ abs b'

-- Conversion is sound and complete with respect to definitional equality,
-- making conversion an appropriate implementation of definitional equality

⇒-≈ : ∀ {a b} → a ⇒ b → a ≈ b
⇒-≈ (⇒-β b⇒b' a⇒a') = ≈-trans (≈-$ᵈ (≈-λᵈ (⇒-≈ b⇒b')) (⇒-≈ a⇒a')) ≈-β
⇒-≈ (⇒-var s) = ≈-refl
⇒-≈ ⇒-∗ = ≈-refl
⇒-≈ (⇒-Π a⇒a' b⇒b') = ≈-Π (⇒-≈ a⇒a') (⇒-≈ b⇒b')
⇒-≈ (⇒-λᵈ b⇒b') = ≈-λᵈ (⇒-≈ b⇒b')
⇒-≈ (⇒-$ᵈ b⇒b' a⇒a') = ≈-$ᵈ (⇒-≈ b⇒b') (⇒-≈ a⇒a')
⇒-≈ ⇒-mty = ≈-refl
⇒-≈ (⇒-abs b⇒b') = ≈-abs (⇒-≈ b⇒b')

⇒⋆-≈ : ∀ {a b} → a ⇒⋆ b → a ≈ b
⇒⋆-≈ (⇒⋆-refl a) = ≈-refl
⇒⋆-≈ (⇒⋆-trans a⇒b b⇒⋆c) = ≈-trans (⇒-≈ a⇒b) (⇒⋆-≈ b⇒⋆c)

⇔-≈ : ∀ {a b} → a ⇔ b → a ≈ b
⇔-≈ (_ , a⇒⋆c , b⇒⋆c) = ≈-trans (⇒⋆-≈ a⇒⋆c) (≈-sym (⇒⋆-≈ b⇒⋆c))

≈-⇔ : ∀ {a b} → a ≈ b → a ⇔ b
≈-⇔ ≈-refl = ⇔-refl
≈-⇔ (≈-sym b≈a) = ⇔-sym (≈-⇔ b≈a)
≈-⇔ (≈-trans a≈b b≈c) = ⇔-trans (≈-⇔ a≈b) (≈-⇔ b≈c)
≈-⇔ ≈-β = ⇒-⇔ (⇒-β (⇒-refl _) (⇒-refl _))
≈-⇔ (≈-Π a≈a' b≈b') = ⇔-Π (≈-⇔ a≈a') (≈-⇔ b≈b')
≈-⇔ (≈-λᵈ b≈b') = ⇔-λᵈ (≈-⇔ b≈b')
≈-⇔ (≈-$ᵈ b≈b' a≈a') = ⇔-$ᵈ (≈-⇔ b≈b') (≈-⇔ a≈a')
≈-⇔ (≈-abs b≈b') = ⇔-abs (≈-⇔ b≈b')

{--------------------------------------------------
  Context well-formedness and term well-typedness
--------------------------------------------------}

infix 10 ⊢_
data ⊢_ : Ctxt → Set
data _⊢_⦂_#_ (Γ : Ctxt) : Term → Term → Level → Set

data ⊢_ where
  ⊢∙ : ⊢ ∙
  ⊢∷ : ∀ {Γ A j} →
       ⊢ Γ →
       Γ ⊢ A ⦂ ∗ # j →
       ---------------
       ⊢ Γ ∷ A # j

data _⊢_⦂_#_ Γ where
  ⊢var : ∀ {x A j k} →
         ⊢ Γ →
         j ≤ k →
         x ⦂ A # j ∈ Γ →
         -----------------
         Γ ⊢ var x ⦂ A # k
  ⊢∗   : ∀ {k} → ⊢ Γ →
         -------------
         Γ ⊢ ∗ ⦂ ∗ # k
  ⊢Π   : ∀ {A j B k} →
         j < k →
         Γ ⊢ A ⦂ ∗ # j →
         Γ ∷ A # j ⊢ B ⦂ ∗ # k →
         ---------------------
         Γ ⊢ Π A j B ⦂ ∗ # k
  ⊢λᵈ  : ∀ {A j B b k} →
         j < k →
         Γ ⊢ A ⦂ ∗ # j →
         Γ ∷ A # j ⊢ b ⦂ B # k →
         -----------------------
         Γ ⊢ λᵈ b ⦂ Π A j B # k
  ⊢$ᵈ  : ∀ {A j B b a k} →
         j < k →
         Γ ⊢ b ⦂ Π A j B # k →
         Γ ⊢ a ⦂ A # j →
         -----------------------------------
         Γ ⊢ $ᵈ b a ⦂ subst (a +: var) B # k
  ⊢mty : ∀ {k} → ⊢ Γ →
         ---------------
         Γ ⊢ mty ⦂ ∗ # k
  ⊢abs : ∀ {A b k} →
         Γ ⊢ A ⦂ ∗ # k →
         Γ ⊢ b ⦂ mty # k →
         -----------------
         Γ ⊢ abs b ⦂ A # k
  ⊢≈   : ∀ {A B a k} →
         A ≈ B →
         Γ ⊢ a ⦂ A # k →
         Γ ⊢ B ⦂ ∗ # k →
         -------------
         Γ ⊢ a ⦂ B # k

cumulativity : ∀ {Γ a A j k} → j < k → Γ ⊢ a ⦂ A # j → Γ ⊢ a ⦂ A # k
cumulativity j<k (⊢var ⊢Γ eq where?) = ⊢var ⊢Γ (lt j<k) where?
cumulativity j<k (⊢var ⊢Γ (lt i<j) where?) = ⊢var ⊢Γ (lt (trans< i<j j<k)) where?
cumulativity j<k (⊢∗ ⊢Γ) = ⊢∗ ⊢Γ
cumulativity j<k (⊢Π i<j A B) = ⊢Π (trans< i<j j<k) A (cumulativity j<k B)
cumulativity j<k (⊢λᵈ i<j A b) = ⊢λᵈ (trans< i<j j<k) A (cumulativity j<k b)
cumulativity j<k (⊢$ᵈ i<j b a) = ⊢$ᵈ (trans< i<j j<k) (cumulativity j<k b) a
cumulativity j<k (⊢mty ⊢Γ) = ⊢mty ⊢Γ
cumulativity j<k (⊢abs A b) = ⊢abs (cumulativity j<k A) (cumulativity j<k b)
cumulativity j<k (⊢≈ A≈B a B) = ⊢≈ A≈B (cumulativity j<k a) (cumulativity j<k B)