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
  ≈-Π     : ∀ {a a' b b'} →
            a ≈ a' →
            b ≈ b' →
            -------------------
            Π a b ≈ Π a' b'
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
⇒-≈ (⇒-𝒰 k) = ≈-refl
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
data _⊢_⦂_ (Γ : Ctxt) : Term → Term → Set

data ⊢_ where
  ⊢∙ : ⊢ ∙
  ⊢∷ : ∀ {Γ A k} →
       ⊢ Γ →
       Γ ⊢ A ⦂ 𝒰 k →
       ---------------
       ⊢ Γ ∷ A

data _⊢_⦂_ Γ where
  ⊢var : ∀ {x A} →
         ⊢ Γ →
         x ⦂ A ∈ Γ →
         -------------
         Γ ⊢ var x ⦂ A
  ⊢𝒰   : ∀ {j k} → ⊢ Γ →
         j < k →
         ---------------
         Γ ⊢ 𝒰 j ⦂ 𝒰 k
  ⊢Π   : ∀ {A B k} →
         Γ ⊢ A ⦂ 𝒰 k →
         Γ ∷ A ⊢ B ⦂ 𝒰 k →
         -----------------
         Γ ⊢ Π A B ⦂ 𝒰 k
  ⊢λᵈ  : ∀ {A B b k} →
         Γ ⊢ Π A B ⦂ 𝒰 k →
         Γ ∷ A ⊢ b ⦂ B →
         ----------------
         Γ ⊢ λᵈ b ⦂ Π A B
  ⊢$ᵈ  : ∀ {A B b a} →
         Γ ⊢ b ⦂ Π A B →
         Γ ⊢ a ⦂ A →
         -------------------------------
         Γ ⊢ $ᵈ b a ⦂ subst (a +: var) B
  ⊢mty : ∀ {k} → ⊢ Γ →
         ---------------
         Γ ⊢ mty ⦂ 𝒰 k
  ⊢abs : ∀ {A b k} →
         Γ ⊢ A ⦂ 𝒰 k →
         Γ ⊢ b ⦂ mty →
         -------------
         Γ ⊢ abs b ⦂ A
  ⊢≈   : ∀ {A B a k} →
         A ≈ B →
         Γ ⊢ a ⦂ A →
         Γ ⊢ B ⦂ 𝒰 k →
         -------------
         Γ ⊢ a ⦂ B