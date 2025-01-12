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
  ≈-ι     : ∀ {d} →
            ------------
            J d refl ≈ d
  ≈-ift   : ∀ {a c} →
            ----------------
            if true a c ≈ a
  ≈-iff   : ∀ {a c} →
            ----------------
            if false a c ≈ c
  ≈-Π     : ∀ {a a' b b'} →
            a ≈ a' →
            b ≈ b' →
            ---------------
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
  ≈-eq    : ∀ {A A' a a' b b'} →
            A ≈ A' →
            a ≈ a' →
            b ≈ b' →
            ----------------------
            eq A a b ≈ eq A' a' b'
  ≈-J     : ∀ {d d' p p'} →
            d ≈ d' →
            p ≈ p' →
            ---------------
            J d p ≈ J d' p'
  ≈-if    : ∀ {b b' a a' c c'} →
            b ≈ b' →
            a ≈ a' →
            c ≈ c' →
            ----------------------
            if b a c ≈ if b' a' c'

-- Conversion is sound and complete with respect to definitional equality,
-- making conversion an appropriate implementation of definitional equality

⇒-≈ : ∀ {a b} → a ⇒ b → a ≈ b
⇒-≈ (⇒-β b⇒b' a⇒a') = ≈-trans (≈-$ᵈ (≈-λᵈ (⇒-≈ b⇒b')) (⇒-≈ a⇒a')) ≈-β
⇒-≈ (⇒-ι d⇒d') = ≈-trans (≈-J (⇒-≈ d⇒d') ≈-refl) ≈-ι
⇒-≈ (⇒-ift a⇒a') = ≈-trans (≈-if ≈-refl (⇒-≈ a⇒a') ≈-refl) ≈-ift
⇒-≈ (⇒-iff c⇒c') = ≈-trans (≈-if ≈-refl ≈-refl (⇒-≈ c⇒c')) ≈-iff
⇒-≈ (⇒-var s) = ≈-refl
⇒-≈ (⇒-𝒰 k) = ≈-refl
⇒-≈ (⇒-Π a⇒a' b⇒b') = ≈-Π (⇒-≈ a⇒a') (⇒-≈ b⇒b')
⇒-≈ (⇒-λᵈ b⇒b') = ≈-λᵈ (⇒-≈ b⇒b')
⇒-≈ (⇒-$ᵈ b⇒b' a⇒a') = ≈-$ᵈ (⇒-≈ b⇒b') (⇒-≈ a⇒a')
⇒-≈ ⇒-mty = ≈-refl
⇒-≈ (⇒-abs b⇒b') = ≈-abs (⇒-≈ b⇒b')
⇒-≈ (⇒-eq A⇒A' a⇒a' b⇒b') = ≈-eq (⇒-≈ A⇒A') (⇒-≈ a⇒a') (⇒-≈ b⇒b')
⇒-≈ ⇒-rfl = ≈-refl
⇒-≈ (⇒-J d⇒d' p⇒p') = ≈-J (⇒-≈ d⇒d') (⇒-≈ p⇒p')
⇒-≈ ⇒-𝔹 = ≈-refl
⇒-≈ ⇒-true = ≈-refl
⇒-≈ ⇒-false = ≈-refl
⇒-≈ (⇒-if b⇒b' a⇒a' c⇒c') = ≈-if (⇒-≈ b⇒b') (⇒-≈ a⇒a') (⇒-≈ c⇒c')

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
≈-⇔ ≈-ι = ⇒-⇔ (⇒-ι (⇒-refl _))
≈-⇔ ≈-ift = ⇒-⇔ (⇒-ift (⇒-refl _))
≈-⇔ ≈-iff = ⇒-⇔ (⇒-iff (⇒-refl _))
≈-⇔ (≈-Π a≈a' b≈b') = ⇔-Π (≈-⇔ a≈a') (≈-⇔ b≈b')
≈-⇔ (≈-λᵈ b≈b') = ⇔-λᵈ (≈-⇔ b≈b')
≈-⇔ (≈-$ᵈ b≈b' a≈a') = ⇔-$ᵈ (≈-⇔ b≈b') (≈-⇔ a≈a')
≈-⇔ (≈-abs b≈b') = ⇔-abs (≈-⇔ b≈b')
≈-⇔ (≈-eq A≈A' a≈a' b≈b') = ⇔-eq (≈-⇔ A≈A') (≈-⇔ a≈a') (≈-⇔ b≈b')
≈-⇔ (≈-J d≈d' p≈p') = ⇔-J (≈-⇔ d≈d') (≈-⇔ p≈p')
≈-⇔ (≈-if b≈b' a≈a' c≈c') = ⇔-if (≈-⇔ b≈b') (≈-⇔ a≈a') (≈-⇔ c≈c')

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
  ⊢var    : ∀ {x A} →
            ⊢ Γ →
            x ⦂ A ∈ Γ →
            -------------
            Γ ⊢ var x ⦂ A
  ⊢𝒰      : ∀ {j k} → ⊢ Γ →
            j < k →
            ---------------
            Γ ⊢ 𝒰 j ⦂ 𝒰 k
  ⊢Π      : ∀ {A B k} →
            Γ ⊢ A ⦂ 𝒰 k →
            Γ ∷ A ⊢ B ⦂ 𝒰 k →
            -----------------
            Γ ⊢ Π A B ⦂ 𝒰 k
  ⊢λᵈ     : ∀ {A B b k} →
            Γ ⊢ Π A B ⦂ 𝒰 k →
            Γ ∷ A ⊢ b ⦂ B →
            ----------------
            Γ ⊢ λᵈ b ⦂ Π A B
  ⊢$ᵈ     : ∀ {A B b a} →
            Γ ⊢ b ⦂ Π A B →
            Γ ⊢ a ⦂ A →
            -------------------------------
            Γ ⊢ $ᵈ b a ⦂ subst (a +: var) B
  ⊢mty    : ∀ {k} → ⊢ Γ →
            ---------------
            Γ ⊢ mty ⦂ 𝒰 k
  ⊢abs    : ∀ {A b k} →
            Γ ⊢ A ⦂ 𝒰 k →
            Γ ⊢ b ⦂ mty →
            -------------
            Γ ⊢ abs b ⦂ A
  ⊢eq     : ∀ {A a b k} →
            Γ ⊢ A ⦂ 𝒰 k →
            Γ ⊢ a ⦂ A →
            Γ ⊢ b ⦂ A →
            -------------------
            Γ ⊢ eq A a b ⦂ 𝒰 k
  ⊢refl   : ∀ {A a} →
            Γ ⊢ a ⦂ A →
            -------------------
            Γ ⊢ refl ⦂ eq A a a
  ⊢J      : ∀ {A a b p d B k} →
            Γ ⊢ p ⦂ eq A a b →
            Γ ∷ A ∷ eq (rename suc A) (rename suc a) (var 0) ⊢ B ⦂ 𝒰 k →
            Γ ⊢ d ⦂ subst (refl +: a +: var) B →
            ------------------------------------
            Γ ⊢ J d p ⦂ subst (p +: b +: var) B
  ⊢𝔹      : ∀ {k} → ⊢ Γ →
            -------------
            Γ ⊢ 𝔹 ⦂ 𝒰 k
  ⊢true   : ⊢ Γ →
            ------------
            Γ ⊢ true ⦂ 𝔹
  ⊢false  : ⊢ Γ →
            -------------
            Γ ⊢ false ⦂ 𝔹
  ⊢if     : ∀ {A b a c k} →
            Γ ∷ 𝔹 ⊢ A ⦂ 𝒰 k →
            Γ ⊢ b ⦂ 𝔹 →
            Γ ⊢ a ⦂ subst (true +: var) A →
            Γ ⊢ c ⦂ subst (false +: var) A →
            ---------------------------------
            Γ ⊢ if b a c ⦂ subst (b +: var) A
  ⊢≈      : ∀ {A B a k} →
            A ≈ B →
            Γ ⊢ a ⦂ A →
            Γ ⊢ B ⦂ 𝒰 k →
            -------------
            Γ ⊢ a ⦂ B