open import common
import syntactics

module reduction (Level : Set) where
open syntactics Level

{---------------------
  Parallel reduction
---------------------}

data _⇒_ : Term → Term → Set where
  ⇒-β     : ∀ {b b' a a'} →
            b ⇒ b' →
            a ⇒ a' →
            ----------------------------------
            $ᵈ (λᵈ b) a ⇒ subst (a' +: var) b'
  ⇒-ι     : ∀ {d d'} →
            d ⇒ d' →
            -------------
            J d refl ⇒ d'
  ⇒-ift   : ∀ {a a' c} →
            a ⇒ a' →
            ----------------
            if true a c ⇒ a'
  ⇒-iff   : ∀ {a c c'} →
            c ⇒ c' →
            -----------------
            if false a c ⇒ c'
  ⇒-var   : ∀ s → var s ⇒ var s
  ⇒-𝒰     : ∀ k → 𝒰 k ⇒ 𝒰 k
  ⇒-Π     : ∀ {a a' b b'} →
            a ⇒ a' →
            b ⇒ b' →
            -------------------
            Π a b ⇒ Π a' b'
  ⇒-λᵈ    : ∀ {b b'} →
            b ⇒ b' →
            ------------
            λᵈ b ⇒ λᵈ b'
  ⇒-$ᵈ    : ∀ {b b' a a'} →
            b ⇒ b' →
            a ⇒ a' →
            -----------------
            $ᵈ b a ⇒ $ᵈ b' a'
  ⇒-mty   : mty ⇒ mty
  ⇒-abs   : ∀ {b b'} →
            b ⇒ b' →
            --------------
            abs b ⇒ abs b'
  ⇒-eq    : ∀ {A A' a a' b b'} →
            A ⇒ A' →
            a ⇒ a' →
            b ⇒ b' →
            ----------------------
            eq A a b ⇒ eq A' a' b'
  ⇒-rfl   : refl ⇒ refl
  ⇒-J     : ∀ {d d' p p'} →
            d ⇒ d' →
            p ⇒ p' →
            ---------------
            J d p ⇒ J d' p'
  ⇒-𝔹     : 𝔹 ⇒ 𝔹
  ⇒-true  : true ⇒ true
  ⇒-false : false ⇒ false
  ⇒-if    : ∀ {b b' a a' c c'} →
            b ⇒ b' →
            a ⇒ a' →
            c ⇒ c' →
            ----------------------
            if b a c ⇒ if b' a' c'

⇒-refl : ∀ a → a ⇒ a
⇒-refl (var s) = ⇒-var s
⇒-refl (𝒰 k) = ⇒-𝒰 k
⇒-refl (Π a b) = ⇒-Π (⇒-refl a) (⇒-refl b)
⇒-refl (λᵈ b) = ⇒-λᵈ (⇒-refl b)
⇒-refl ($ᵈ b a) = ⇒-$ᵈ (⇒-refl b) (⇒-refl a)
⇒-refl mty = ⇒-mty
⇒-refl (abs b) = ⇒-abs (⇒-refl b)
⇒-refl (eq A a b) = ⇒-eq (⇒-refl A) (⇒-refl a) (⇒-refl b)
⇒-refl refl = ⇒-rfl
⇒-refl (J d p) = ⇒-J (⇒-refl d) (⇒-refl p)
⇒-refl 𝔹 = ⇒-𝔹
⇒-refl true = ⇒-true
⇒-refl false = ⇒-false
⇒-refl (if b a c) = ⇒-if (⇒-refl b) (⇒-refl a) (⇒-refl c)

⇒-rename : ∀ {a b} ξ → a ⇒ b → rename ξ a ⇒ rename ξ b
⇒-rename ξ (⇒-β {b} {b'} {a} {a'} b⇒b' a⇒a') =
  transp (_ ⇒_) (renameDist ξ a' b') h where
  h : $ᵈ (λᵈ (rename (lift ξ) b)) (rename ξ a) ⇒ subst (rename ξ a' +: var) (rename (lift ξ) b')
  h = ⇒-β (⇒-rename (lift ξ) b⇒b') (⇒-rename ξ a⇒a')
⇒-rename ξ (⇒-ι d⇒d') = ⇒-ι (⇒-rename ξ d⇒d')
⇒-rename ξ (⇒-ift a⇒a') = ⇒-ift (⇒-rename ξ a⇒a')
⇒-rename ξ (⇒-iff c⇒c') = ⇒-iff (⇒-rename ξ c⇒c')
⇒-rename ξ (⇒-var s) = ⇒-var (ξ s)
⇒-rename ξ (⇒-𝒰 k) = ⇒-𝒰 k
⇒-rename ξ (⇒-Π a⇒a' b⇒b') = ⇒-Π (⇒-rename ξ a⇒a') (⇒-rename (lift ξ) b⇒b')
⇒-rename ξ (⇒-λᵈ b⇒b') = ⇒-λᵈ (⇒-rename (lift ξ) b⇒b')
⇒-rename ξ (⇒-$ᵈ b⇒b' a⇒a') = ⇒-$ᵈ (⇒-rename ξ b⇒b') (⇒-rename ξ a⇒a')
⇒-rename ξ ⇒-mty = ⇒-mty
⇒-rename ξ (⇒-abs b⇒b') = ⇒-abs (⇒-rename ξ b⇒b')
⇒-rename ξ (⇒-eq A⇒A' a⇒a' b⇒b') = ⇒-eq (⇒-rename ξ A⇒A') (⇒-rename ξ a⇒a') (⇒-rename ξ b⇒b')
⇒-rename ξ ⇒-rfl = ⇒-rfl
⇒-rename ξ (⇒-J d⇒d' p⇒p') = ⇒-J (⇒-rename ξ d⇒d') (⇒-rename ξ p⇒p')
⇒-rename ξ ⇒-𝔹 = ⇒-𝔹
⇒-rename ξ ⇒-true = ⇒-true
⇒-rename ξ ⇒-false = ⇒-false
⇒-rename ξ (⇒-if b⇒b' a⇒a' c⇒c') = ⇒-if (⇒-rename ξ b⇒b') (⇒-rename ξ a⇒a') (⇒-rename ξ c⇒c')

⇒-lift : ∀ {σ τ} → (∀ x → σ x ⇒ τ x) → ∀ x → (↑ σ) x ⇒ (↑ τ) x
⇒-lift r zero = ⇒-var 0
⇒-lift r (suc n) = ⇒-rename suc (r n)

⇒-morphing : ∀ {a b} σ τ → (∀ x → σ x ⇒ τ x) → a ⇒ b → subst σ a ⇒ subst τ b
⇒-morphing σ τ r (⇒-β {b} {b'} {a} {a'} b⇒b' a⇒a') =
  transp (subst σ ($ᵈ (λᵈ b) a) ⇒_) (substDist τ a' b') h where
  h : $ᵈ (λᵈ (subst (↑ σ) b)) (subst σ a) ⇒ subst (subst τ a' +: var) (subst (↑ τ) b')
  h = ⇒-β (⇒-morphing (↑ σ) (↑ τ) (⇒-lift r) b⇒b') (⇒-morphing σ τ r a⇒a')
⇒-morphing σ τ r (⇒-ι d⇒d') = ⇒-ι (⇒-morphing σ τ r d⇒d')
⇒-morphing σ τ r (⇒-ift a⇒a') = ⇒-ift (⇒-morphing σ τ r a⇒a')
⇒-morphing σ τ r (⇒-iff c⇒c') = ⇒-iff (⇒-morphing σ τ r c⇒c')
⇒-morphing σ τ r (⇒-var s) = r s
⇒-morphing σ τ r (⇒-𝒰 k) = ⇒-𝒰 k
⇒-morphing σ τ r (⇒-Π a⇒a' b⇒b') = ⇒-Π (⇒-morphing σ τ r a⇒a') (⇒-morphing (↑ σ) (↑ τ) (⇒-lift r) b⇒b')
⇒-morphing σ τ r (⇒-λᵈ b⇒b') = ⇒-λᵈ (⇒-morphing (↑ σ) (↑ τ) (⇒-lift r) b⇒b')
⇒-morphing σ τ r (⇒-$ᵈ b⇒b' a⇒a') = ⇒-$ᵈ (⇒-morphing σ τ r b⇒b') (⇒-morphing σ τ r a⇒a')
⇒-morphing σ τ r ⇒-mty = ⇒-mty
⇒-morphing σ τ r (⇒-abs b⇒b') = ⇒-abs (⇒-morphing σ τ r b⇒b')
⇒-morphing σ τ r (⇒-eq A⇒A' a⇒a' b⇒b') = ⇒-eq (⇒-morphing σ τ r A⇒A') (⇒-morphing σ τ r a⇒a') (⇒-morphing σ τ r b⇒b')
⇒-morphing σ τ r ⇒-rfl = ⇒-rfl
⇒-morphing σ τ r (⇒-J d⇒d' p⇒p') = ⇒-J (⇒-morphing σ τ r d⇒d') (⇒-morphing σ τ r p⇒p')
⇒-morphing σ τ r ⇒-𝔹 = ⇒-𝔹
⇒-morphing σ τ r ⇒-true = ⇒-true
⇒-morphing σ τ r ⇒-false = ⇒-false
⇒-morphing σ τ r (⇒-if b⇒b' a⇒a' c⇒c') = ⇒-if (⇒-morphing σ τ r b⇒b') (⇒-morphing σ τ r a⇒a') (⇒-morphing σ τ r c⇒c')

⇒-subst : ∀ {a b} σ → a ⇒ b → subst σ a ⇒ subst σ b
⇒-subst σ r = ⇒-morphing σ σ (λ x → ⇒-refl (σ x)) r

⇒-cong : ∀ {a a' b b'} → a ⇒ a' → b ⇒ b' → subst (a +: var) b ⇒ subst (a' +: var) b'
⇒-cong {a} {a'} a⇒a' b⇒b' = ⇒-morphing (a +: var) (a' +: var) (λ {zero → a⇒a' ; (suc n) → ⇒-var n}) b⇒b'

⇒-cong₂ : ∀ {a a' b b'} c → a ⇒ a' → b ⇒ b' → subst (a +: b +: var) c ⇒ subst (a' +: b' +: var) c
⇒-cong₂ {a} {a'} {b} {b'} c a⇒a' b⇒b' =
  ⇒-morphing (a +: b +: var) (a' +: b' +: var)
    (λ {zero → a⇒a' ; (suc zero) → b⇒b' ; (suc (suc n)) → ⇒-var n}) (⇒-refl c)

{--------------------------------
  Reflexive, transitive closure
  of parallel reduction
--------------------------------}

data _⇒⋆_ : Term → Term → Set where
  ⇒⋆-refl : ∀ a → a ⇒⋆ a
  ⇒⋆-trans : ∀ {a b c} → a ⇒ b → b ⇒⋆ c → a ⇒⋆ c

⇒-⇒⋆ : ∀ {a b} → a ⇒ b → a ⇒⋆ b
⇒-⇒⋆ a⇒b = ⇒⋆-trans a⇒b (⇒⋆-refl _)

⇒⋆-trans' : ∀ {a b c} → a ⇒⋆ b → b ⇒⋆ c → a ⇒⋆ c
⇒⋆-trans' (⇒⋆-refl _) b⇒⋆c = b⇒⋆c
⇒⋆-trans' (⇒⋆-trans a⇒b b⇒⋆c) c⇒⋆d = ⇒⋆-trans a⇒b (⇒⋆-trans' b⇒⋆c c⇒⋆d)

⇒⋆-rename : ∀ {a b} ξ → a ⇒⋆ b → rename ξ a ⇒⋆ rename ξ b
⇒⋆-rename ξ (⇒⋆-refl a) = ⇒⋆-refl (rename ξ a)
⇒⋆-rename ξ (⇒⋆-trans a⇒b b⇒⋆c) = ⇒⋆-trans (⇒-rename ξ a⇒b) (⇒⋆-rename ξ b⇒⋆c)

⇒⋆-subst : ∀ {a b} σ → a ⇒⋆ b → subst σ a ⇒⋆ subst σ b
⇒⋆-subst σ (⇒⋆-refl a) = ⇒⋆-refl (subst σ a)
⇒⋆-subst σ (⇒⋆-trans a⇒b b⇒⋆c) = ⇒⋆-trans (⇒-subst σ a⇒b) (⇒⋆-subst σ b⇒⋆c)

⇒⋆-cong : ∀ {a a' b b'} → a ⇒⋆ a' → b ⇒⋆ b' → subst (a +: var) b ⇒⋆ subst (a' +: var) b'
⇒⋆-cong (⇒⋆-refl a) (⇒⋆-refl b) = ⇒⋆-refl (subst (a +: var) b)
⇒⋆-cong (⇒⋆-refl a) (⇒⋆-trans b⇒c c⇒⋆d) = ⇒⋆-trans (⇒-cong (⇒-refl a) b⇒c) (⇒⋆-cong (⇒⋆-refl a) c⇒⋆d)
⇒⋆-cong (⇒⋆-trans a⇒b b⇒⋆c) (⇒⋆-refl d) = ⇒⋆-trans (⇒-cong a⇒b (⇒-refl d)) (⇒⋆-cong b⇒⋆c (⇒⋆-refl d))
⇒⋆-cong (⇒⋆-trans a⇒b b⇒⋆c) (⇒⋆-trans d⇒e e⇒⋆f) = ⇒⋆-trans (⇒-cong a⇒b d⇒e) (⇒⋆-cong b⇒⋆c e⇒⋆f)

⇒⋆-cong₂ : ∀ {a a' b b'} c → a ⇒⋆ a' → b ⇒⋆ b' → subst (a +: b +: var) c ⇒⋆ subst (a' +: b' +: var) c
⇒⋆-cong₂ x (⇒⋆-refl a) (⇒⋆-refl b) = ⇒⋆-refl (subst (a +: b +: var) x)
⇒⋆-cong₂ x (⇒⋆-refl a) (⇒⋆-trans b⇒c c⇒⋆d) = ⇒⋆-trans (⇒-cong₂ x (⇒-refl a) b⇒c) (⇒⋆-cong₂ x (⇒⋆-refl a) c⇒⋆d)
⇒⋆-cong₂ x (⇒⋆-trans a⇒b b⇒⋆c) (⇒⋆-refl d) = ⇒⋆-trans (⇒-cong₂ x a⇒b (⇒-refl d)) (⇒⋆-cong₂ x b⇒⋆c (⇒⋆-refl d))
⇒⋆-cong₂ x (⇒⋆-trans a⇒b b⇒⋆c) (⇒⋆-trans d⇒e e⇒⋆f) = ⇒⋆-trans (⇒-cong₂ x a⇒b d⇒e) (⇒⋆-cong₂ x b⇒⋆c e⇒⋆f)

⇒⋆-Π : ∀ {a a' b b'} → a ⇒⋆ a' → b ⇒⋆ b' → Π a b ⇒⋆ Π a' b'
⇒⋆-Π (⇒⋆-refl a) (⇒⋆-refl b) = ⇒⋆-refl (Π a b)
⇒⋆-Π (⇒⋆-refl a) (⇒⋆-trans b⇒b' b'⇒⋆b'') = ⇒⋆-trans (⇒-Π (⇒-refl a) b⇒b') (⇒⋆-Π (⇒⋆-refl a) b'⇒⋆b'')
⇒⋆-Π (⇒⋆-trans a⇒a' a'⇒⋆a'') (⇒⋆-refl b) = ⇒⋆-trans (⇒-Π a⇒a' (⇒-refl b)) (⇒⋆-Π a'⇒⋆a'' (⇒⋆-refl b))
⇒⋆-Π (⇒⋆-trans a⇒a' a'⇒⋆a'') (⇒⋆-trans b⇒b' b'⇒⋆b'') = ⇒⋆-trans (⇒-Π a⇒a' b⇒b') (⇒⋆-Π a'⇒⋆a'' b'⇒⋆b'')

⇒⋆-λᵈ : ∀ {b b'} → b ⇒⋆ b' → λᵈ b ⇒⋆ λᵈ b'
⇒⋆-λᵈ (⇒⋆-refl b) = ⇒⋆-refl (λᵈ b)
⇒⋆-λᵈ (⇒⋆-trans b⇒b' b'⇒⋆b'') = ⇒⋆-trans (⇒-λᵈ b⇒b') (⇒⋆-λᵈ b'⇒⋆b'')

⇒⋆-$ᵈ : ∀ {a a' b b'} → b ⇒⋆ b' → a ⇒⋆ a' → $ᵈ b a ⇒⋆ $ᵈ b' a'
⇒⋆-$ᵈ (⇒⋆-refl b) (⇒⋆-refl a) = ⇒⋆-refl ($ᵈ b a)
⇒⋆-$ᵈ (⇒⋆-trans b⇒b' b'⇒⋆b'') (⇒⋆-refl a) = ⇒⋆-trans (⇒-$ᵈ b⇒b' (⇒-refl a)) (⇒⋆-$ᵈ b'⇒⋆b'' (⇒⋆-refl a))
⇒⋆-$ᵈ (⇒⋆-refl b) (⇒⋆-trans a⇒a' a'⇒⋆a'') = ⇒⋆-trans (⇒-$ᵈ (⇒-refl b) a⇒a') (⇒⋆-$ᵈ (⇒⋆-refl b) a'⇒⋆a'')
⇒⋆-$ᵈ (⇒⋆-trans b⇒b' b'⇒⋆b'') (⇒⋆-trans a⇒a' a'⇒⋆a'') = ⇒⋆-trans (⇒-$ᵈ b⇒b' a⇒a') (⇒⋆-$ᵈ b'⇒⋆b'' a'⇒⋆a'')

⇒⋆-abs : ∀ {b b'} → b ⇒⋆ b' → abs b ⇒⋆ abs b'
⇒⋆-abs (⇒⋆-refl b) = ⇒⋆-refl (abs b)
⇒⋆-abs (⇒⋆-trans b⇒b' b'⇒⋆b'') = ⇒⋆-trans (⇒-abs b⇒b') (⇒⋆-abs b'⇒⋆b'')

⇒⋆-eq : ∀ {A A' a a' b b'} → A ⇒⋆ A' → a ⇒⋆ a' → b ⇒⋆ b' → eq A a b ⇒⋆ eq A' a' b'
⇒⋆-eq (⇒⋆-refl A) (⇒⋆-refl a) (⇒⋆-refl b) = ⇒⋆-refl (eq A a b)
⇒⋆-eq (⇒⋆-refl A) (⇒⋆-refl a) (⇒⋆-trans b⇒b' b'⇒⋆b'') = ⇒⋆-trans (⇒-eq (⇒-refl A) (⇒-refl a) b⇒b') (⇒⋆-eq (⇒⋆-refl A) (⇒⋆-refl a) b'⇒⋆b'')
⇒⋆-eq (⇒⋆-refl A) (⇒⋆-trans a⇒a' a'⇒⋆a'') (⇒⋆-refl b) = ⇒⋆-trans (⇒-eq (⇒-refl A) a⇒a' (⇒-refl b)) (⇒⋆-eq (⇒⋆-refl A) a'⇒⋆a'' (⇒⋆-refl b))
⇒⋆-eq (⇒⋆-trans A⇒A' A'⇒⋆A'') (⇒⋆-refl a) (⇒⋆-refl b) = ⇒⋆-trans (⇒-eq A⇒A' (⇒-refl a) (⇒-refl b)) (⇒⋆-eq A'⇒⋆A'' (⇒⋆-refl a) (⇒⋆-refl b))
⇒⋆-eq (⇒⋆-refl A) (⇒⋆-trans a⇒a' a'⇒⋆a'') (⇒⋆-trans b⇒b' b'⇒⋆b'') = ⇒⋆-trans (⇒-eq (⇒-refl A) a⇒a' b⇒b') (⇒⋆-eq (⇒⋆-refl A) a'⇒⋆a'' b'⇒⋆b'')
⇒⋆-eq (⇒⋆-trans A⇒A' A'⇒⋆A'') (⇒⋆-refl a) (⇒⋆-trans b⇒b' b'⇒⋆b'') = ⇒⋆-trans (⇒-eq A⇒A' (⇒-refl a) b⇒b') (⇒⋆-eq A'⇒⋆A'' (⇒⋆-refl a) b'⇒⋆b'')
⇒⋆-eq (⇒⋆-trans A⇒A' A'⇒⋆A'') (⇒⋆-trans a⇒a' a'⇒⋆a'') (⇒⋆-refl b) = ⇒⋆-trans (⇒-eq A⇒A' a⇒a' (⇒-refl b)) (⇒⋆-eq A'⇒⋆A'' a'⇒⋆a'' (⇒⋆-refl b))
⇒⋆-eq (⇒⋆-trans A⇒A' A'⇒⋆A'') (⇒⋆-trans a⇒a' a'⇒⋆a'') (⇒⋆-trans b⇒b' b'⇒⋆b'') = ⇒⋆-trans (⇒-eq A⇒A' a⇒a' b⇒b') (⇒⋆-eq A'⇒⋆A'' a'⇒⋆a'' b'⇒⋆b'')

⇒⋆-J : ∀ {d d' p p'} → d ⇒⋆ d' → p ⇒⋆ p' → J d p ⇒⋆ J d' p'
⇒⋆-J (⇒⋆-refl d) (⇒⋆-refl p) = ⇒⋆-refl (J d p)
⇒⋆-J (⇒⋆-refl d) (⇒⋆-trans p⇒p' p'⇒⋆p'') = ⇒⋆-trans (⇒-J (⇒-refl d) p⇒p') (⇒⋆-J (⇒⋆-refl d) p'⇒⋆p'')
⇒⋆-J (⇒⋆-trans d⇒d' d'⇒⋆d'') (⇒⋆-refl p) = ⇒⋆-trans (⇒-J d⇒d' (⇒-refl p)) (⇒⋆-J d'⇒⋆d'' (⇒⋆-refl p))
⇒⋆-J (⇒⋆-trans d⇒d' d'⇒⋆d'') (⇒⋆-trans p⇒p' p'⇒⋆p'') = ⇒⋆-trans (⇒-J d⇒d' p⇒p') (⇒⋆-J d'⇒⋆d'' p'⇒⋆p'')

⇒⋆-if : ∀ {b b' a a' c c'} → b ⇒⋆ b' → a ⇒⋆ a' → c ⇒⋆ c' → if b a c ⇒⋆ if b' a' c'
⇒⋆-if (⇒⋆-refl b) (⇒⋆-refl a) (⇒⋆-refl c) = ⇒⋆-refl (if b a c)
⇒⋆-if (⇒⋆-refl b) (⇒⋆-refl a) (⇒⋆-trans c⇒c' c'⇒⋆c'') = ⇒⋆-trans (⇒-if (⇒-refl b) (⇒-refl a) c⇒c') (⇒⋆-if (⇒⋆-refl b) (⇒⋆-refl a) c'⇒⋆c'')
⇒⋆-if (⇒⋆-refl b) (⇒⋆-trans a⇒a' a'⇒⋆a'') (⇒⋆-refl c) = ⇒⋆-trans (⇒-if (⇒-refl b) a⇒a' (⇒-refl c)) (⇒⋆-if (⇒⋆-refl b) a'⇒⋆a'' (⇒⋆-refl c))
⇒⋆-if (⇒⋆-trans b⇒b' b'⇒⋆b'') (⇒⋆-refl a) (⇒⋆-refl c) = ⇒⋆-trans (⇒-if b⇒b' (⇒-refl a) (⇒-refl c)) (⇒⋆-if b'⇒⋆b'' (⇒⋆-refl a) (⇒⋆-refl c))
⇒⋆-if (⇒⋆-refl b) (⇒⋆-trans a⇒a' a'⇒⋆a'') (⇒⋆-trans c⇒c' c'⇒⋆c'') = ⇒⋆-trans (⇒-if (⇒-refl b) a⇒a' c⇒c') (⇒⋆-if (⇒⋆-refl b) a'⇒⋆a'' c'⇒⋆c'')
⇒⋆-if (⇒⋆-trans b⇒b' b'⇒⋆b'') (⇒⋆-refl a) (⇒⋆-trans c⇒c' c'⇒⋆c'') = ⇒⋆-trans (⇒-if b⇒b' (⇒-refl a) c⇒c') (⇒⋆-if b'⇒⋆b'' (⇒⋆-refl a) c'⇒⋆c'')
⇒⋆-if (⇒⋆-trans b⇒b' b'⇒⋆b'') (⇒⋆-trans a⇒a' a'⇒⋆a'') (⇒⋆-refl c) = ⇒⋆-trans (⇒-if b⇒b' a⇒a' (⇒-refl c)) (⇒⋆-if b'⇒⋆b'' a'⇒⋆a'' (⇒⋆-refl c))
⇒⋆-if (⇒⋆-trans b⇒b' b'⇒⋆b'') (⇒⋆-trans a⇒a' a'⇒⋆a'') (⇒⋆-trans c⇒c' c'⇒⋆c'') = ⇒⋆-trans (⇒-if b⇒b' a⇒a' c⇒c') (⇒⋆-if b'⇒⋆b'' a'⇒⋆a'' c'⇒⋆c'')

⇒⋆-𝒰-inv : ∀ {k b} → 𝒰 k ⇒⋆ b → b ≡ 𝒰 k
⇒⋆-𝒰-inv (⇒⋆-refl (𝒰 k)) = refl
⇒⋆-𝒰-inv (⇒⋆-trans (⇒-𝒰 k) 𝒰⇒⋆b) = ⇒⋆-𝒰-inv 𝒰⇒⋆b

⇒⋆-mty-inv : ∀ {b} → mty ⇒⋆ b → b ≡ mty
⇒⋆-mty-inv (⇒⋆-refl mty) = refl
⇒⋆-mty-inv (⇒⋆-trans ⇒-mty mty⇒⋆b) = ⇒⋆-mty-inv mty⇒⋆b

⇒⋆-Π-inv : ∀ {a b c} → Π a b ⇒⋆ c → ∃[ a' ] ∃[ b' ] c ≡ Π a' b' × a ⇒⋆ a' × b ⇒⋆ b'
⇒⋆-Π-inv (⇒⋆-refl (Π a b)) = a , b , refl , ⇒⋆-refl a , ⇒⋆-refl b
⇒⋆-Π-inv (⇒⋆-trans (⇒-Π a⇒a' b⇒b') Πab'⇒⋆c) =
  let a'' , b'' , p , a'⇒⋆a'' , b'⇒⋆b'' = ⇒⋆-Π-inv Πab'⇒⋆c
  in a'' , b'' , p , ⇒⋆-trans a⇒a' a'⇒⋆a'' , ⇒⋆-trans b⇒b' b'⇒⋆b''

⇒⋆-eq-inv : ∀ {A a b c} → eq A a b ⇒⋆ c → ∃[ A' ] ∃[ a' ] ∃[ b' ] c ≡ eq A' a' b' × A ⇒⋆ A' × a ⇒⋆ a' × b ⇒⋆ b'
⇒⋆-eq-inv (⇒⋆-refl (eq A a b)) = A , a , b , refl , ⇒⋆-refl A , ⇒⋆-refl a , ⇒⋆-refl b
⇒⋆-eq-inv (⇒⋆-trans (⇒-eq A⇒A' a⇒a' b⇒b') eq'⇒⋆c) =
  let A'' , a'' , b'' , p , A'⇒⋆A'' , a'⇒⋆a'' , b'⇒⋆b'' = ⇒⋆-eq-inv eq'⇒⋆c
  in A'' , a'' , b'' , p , ⇒⋆-trans A⇒A' A'⇒⋆A'' , ⇒⋆-trans a⇒a' a'⇒⋆a'' , ⇒⋆-trans b⇒b' b'⇒⋆b''

⇒⋆-refl-inv : ∀ {p} → refl ⇒⋆ p → p ≡ refl
⇒⋆-refl-inv (⇒⋆-refl refl) = refl
⇒⋆-refl-inv (⇒⋆-trans ⇒-rfl refl⇒⋆p) = ⇒⋆-refl-inv refl⇒⋆p

⇒⋆-𝔹-inv : ∀ {B} → 𝔹 ⇒⋆ B → B ≡ 𝔹
⇒⋆-𝔹-inv (⇒⋆-refl 𝔹) = refl
⇒⋆-𝔹-inv (⇒⋆-trans ⇒-𝔹 𝔹⇒⋆B) = ⇒⋆-𝔹-inv 𝔹⇒⋆B

⇒⋆-true-inv : ∀ {b} → true ⇒⋆ b → b ≡ true
⇒⋆-true-inv (⇒⋆-refl true) = refl
⇒⋆-true-inv (⇒⋆-trans ⇒-true true⇒⋆b) = ⇒⋆-true-inv true⇒⋆b

⇒⋆-false-inv : ∀ {b} → false ⇒⋆ b → b ≡ false
⇒⋆-false-inv (⇒⋆-refl false) = refl
⇒⋆-false-inv (⇒⋆-trans ⇒-false false⇒⋆b) = ⇒⋆-false-inv false⇒⋆b

⇒⋆-β : ∀ σ b a → ($ᵈ (λᵈ (subst (↑ σ) b)) a) ⇒⋆ (subst (a +: σ) b)
⇒⋆-β σ b a = ⇒⋆-trans (⇒-β (⇒-refl _) (⇒-refl _))
                      (transp (_⇒⋆ subst (a +: σ) b) (substUnion σ a b) (⇒⋆-refl _))

⇒⋆-ι : ∀ d → J d refl ⇒⋆ d
⇒⋆-ι d = ⇒-⇒⋆ (⇒-ι (⇒-refl d))

{----------------------------------
  Confluence via diamond property
----------------------------------}

diamond : ∀ {a b c} → a ⇒ b → a ⇒ c → ∃[ d ] b ⇒ d × c ⇒ d
diamond (⇒-β b⇒b₁ a⇒a₁) (⇒-$ᵈ (⇒-λᵈ b⇒b₂) a⇒a₂) =
  let b' , b₁⇒b' , b₂⇒b' = diamond b⇒b₁ b⇒b₂
      a' , a₁⇒a' , a₂⇒a' = diamond a⇒a₁ a⇒a₂
  in subst (a' +: var) b' , ⇒-cong a₁⇒a' b₁⇒b' , ⇒-β b₂⇒b' a₂⇒a'
diamond (⇒-$ᵈ (⇒-λᵈ b⇒b₁) a⇒a₁) (⇒-β b⇒b₂ a⇒a₂) =
  let b' , b₁⇒b' , b₂⇒b' = diamond b⇒b₁ b⇒b₂
      a' , a₁⇒a' , a₂⇒a' = diamond a⇒a₁ a⇒a₂
  in subst (a' +: var) b' , ⇒-β b₁⇒b' a₁⇒a' , ⇒-cong a₂⇒a' b₂⇒b'
diamond (⇒-β b⇒b₁ a⇒a₁) (⇒-β b⇒b₂ a⇒a₂) =
  let b' , b₁⇒b' , b₂⇒b' = diamond b⇒b₁ b⇒b₂
      a' , a₁⇒a' , a₂⇒a' = diamond a⇒a₁ a⇒a₂
  in subst (a' +: var) b' , ⇒-cong a₁⇒a' b₁⇒b' , ⇒-cong a₂⇒a' b₂⇒b'
diamond (⇒-ι d⇒d₁) (⇒-J d⇒d₂ ⇒-rfl) =
  let d' , d₁⇒d' , d₂⇒d' = diamond d⇒d₁ d⇒d₂
  in d' , d₁⇒d' , ⇒-ι d₂⇒d'
diamond (⇒-J d⇒d₁ ⇒-rfl) (⇒-ι d⇒d₂) =
  let d' , d₁⇒d' , d₂⇒d' = diamond d⇒d₁ d⇒d₂
  in d' , ⇒-ι d₁⇒d' , d₂⇒d'
diamond (⇒-ι d⇒d₁) (⇒-ι d⇒d₂) =
  let d' , d₁⇒d' , d₂⇒d' = diamond d⇒d₁ d⇒d₂
  in d' , d₁⇒d' , d₂⇒d'
diamond (⇒-ift a⇒a₁) (⇒-if ⇒-true a⇒a₂ c⇒c₂) =
  let a' , a₁⇒a' , a₂⇒a' = diamond a⇒a₁ a⇒a₂
  in a' , a₁⇒a' , ⇒-ift a₂⇒a'
diamond (⇒-iff c⇒c₁) (⇒-if ⇒-false a⇒a₂ c⇒c₂) =
  let c' , c₁⇒c' , c₂⇒c' = diamond c⇒c₁ c⇒c₂
  in c' , c₁⇒c' , ⇒-iff c₂⇒c'
diamond (⇒-if ⇒-true a⇒a₁ c⇒c₁) (⇒-ift a⇒a₂) =
  let a' , a₁⇒a' , a₂⇒a' = diamond a⇒a₁ a⇒a₂
  in a' , ⇒-ift a₁⇒a' , a₂⇒a'
diamond (⇒-if ⇒-false a⇒a₁ c⇒c₁) (⇒-iff c⇒c₂) =
  let c' , c₁⇒c' , c₂⇒c' = diamond c⇒c₁ c⇒c₂
  in c' , ⇒-iff c₁⇒c' , c₂⇒c'
diamond (⇒-ift a⇒a₁) (⇒-ift a⇒a₂) = diamond a⇒a₁ a⇒a₂
diamond (⇒-iff c⇒c₁) (⇒-iff c⇒c₂) = diamond c⇒c₁ c⇒c₂
diamond (⇒-var s) (⇒-var s) = var s , ⇒-var s , ⇒-var s
diamond (⇒-𝒰 k) (⇒-𝒰 k) = (𝒰 k) , ⇒-𝒰 k , ⇒-𝒰 k
diamond (⇒-Π a⇒a₁ b⇒b₁) (⇒-Π a⇒a₂ b⇒b₂) =
  let a' , a₁⇒a' , a₂⇒a' = diamond a⇒a₁ a⇒a₂
      b' , b₁⇒b' , b₂⇒b' = diamond b⇒b₁ b⇒b₂
  in Π a' b' , ⇒-Π a₁⇒a' b₁⇒b' , ⇒-Π a₂⇒a' b₂⇒b'
diamond (⇒-λᵈ b⇒b₁) (⇒-λᵈ b⇒b₂) =
  let b' , b₁⇒b' , b₂⇒b' = diamond b⇒b₁ b⇒b₂
  in λᵈ b' , ⇒-λᵈ b₁⇒b' , ⇒-λᵈ b₂⇒b'
diamond (⇒-$ᵈ b⇒b₁ a⇒a₁) (⇒-$ᵈ b⇒b₂ a⇒a₂) =
  let b' , b₁⇒b' , b₂⇒b' = diamond b⇒b₁ b⇒b₂
      a' , a₁⇒a' , a₂⇒a' = diamond a⇒a₁ a⇒a₂
  in $ᵈ b' a' , ⇒-$ᵈ b₁⇒b' a₁⇒a' , ⇒-$ᵈ b₂⇒b' a₂⇒a'
diamond ⇒-mty ⇒-mty = mty , ⇒-mty , ⇒-mty
diamond (⇒-abs b⇒c) (⇒-abs b⇒d) =
  let e , c⇒e , d⇒e = diamond b⇒c b⇒d
  in abs e , ⇒-abs c⇒e , ⇒-abs d⇒e
diamond (⇒-eq A⇒A₁ a⇒a₁ b⇒b₁) (⇒-eq A⇒A₂ a⇒a₂ b⇒b₂) =
  let A' , A₁⇒A' , A₂⇒A' = diamond A⇒A₁ A⇒A₂
      a' , a₁⇒a' , a₂⇒a' = diamond a⇒a₁ a⇒a₂
      b' , b₁⇒b' , b₂⇒b' = diamond b⇒b₁ b⇒b₂
  in eq A' a' b' , ⇒-eq A₁⇒A' a₁⇒a' b₁⇒b' , ⇒-eq A₂⇒A' a₂⇒a' b₂⇒b'
diamond ⇒-rfl ⇒-rfl = refl , ⇒-rfl , ⇒-rfl
diamond (⇒-J d⇒d₁ p⇒p₁) (⇒-J d⇒d₂ p⇒p₂) =
  let d' , d₁⇒d' , d₂⇒d' = diamond d⇒d₁ d⇒d₂
      p' , p₁⇒p' , p₂⇒p' = diamond p⇒p₁ p⇒p₂
  in J d' p' , ⇒-J d₁⇒d' p₁⇒p' , ⇒-J d₂⇒d' p₂⇒p'
diamond ⇒-𝔹 ⇒-𝔹 = 𝔹 , ⇒-𝔹 , ⇒-𝔹
diamond ⇒-true ⇒-true = true , ⇒-true , ⇒-true
diamond ⇒-false ⇒-false = false , ⇒-false , ⇒-false
diamond (⇒-if b⇒b₁ a⇒a₁ c⇒c₁) (⇒-if b⇒b₂ a⇒a₂ c⇒c₂) =
  let b' , b₁⇒b' , b₂⇒b' = diamond b⇒b₁ b⇒b₂
      a' , a₁⇒a' , a₂⇒a' = diamond a⇒a₁ a⇒a₂
      c' , c₁⇒c' , c₂⇒c' = diamond c⇒c₁ c⇒c₂
  in if b' a' c' , ⇒-if b₁⇒b' a₁⇒a' c₁⇒c' , ⇒-if b₂⇒b' a₂⇒a' c₂⇒c'

{---------------------------------
    a
   / \
  b   d  by the diamond property
// \ /
c   e  by diacon
\\ //
  f
---------------------------------}

diacon : ∀ {a b c} → a ⇒⋆ b → a ⇒ c → ∃[ d ] b ⇒⋆ d × c ⇒⋆ d
diacon {a} {a} {c} (⇒⋆-refl a) a⇒c = c , ⇒-⇒⋆ a⇒c , ⇒⋆-refl c
diacon (⇒⋆-trans a⇒b b⇒⋆c) a⇒d =
  let e , b⇒e  , d⇒e  = diamond a⇒b a⇒d
      f , c⇒⋆f , e⇒⋆f = diacon b⇒⋆c b⇒e
  in f , c⇒⋆f , ⇒⋆-trans d⇒e e⇒⋆f

{---------------------------------
    a
  //  \
 b     c  by diacon
  \\ // \\
    e     d  by confluence
     \\ //
       f
---------------------------------}

confluence : ∀ {a b c} → a ⇒⋆ b → a ⇒⋆ c → ∃[ d ] b ⇒⋆ d × c ⇒⋆ d
confluence {a} {b} {a} a⇒⋆b (⇒⋆-refl a) = b , ⇒⋆-refl b , a⇒⋆b
confluence a⇒⋆b (⇒⋆-trans a⇒c c⇒⋆d) =
  let e , b⇒⋆e , c⇒⋆e = diacon a⇒⋆b a⇒c
      f , e⇒⋆f , d⇒⋆f = confluence c⇒⋆e c⇒⋆d
  in f , ⇒⋆-trans' b⇒⋆e e⇒⋆f , d⇒⋆f

{-----------------------
  Conversion/coherence
-----------------------}

_⇔_ : Term → Term → Set
a ⇔ b = ∃[ c ] a ⇒⋆ c × b ⇒⋆ c

⇒-⇔ : ∀ {a b} → a ⇒ b → a ⇔ b
⇒-⇔ {a} {b} a⇒b = b , ⇒-⇒⋆ a⇒b , ⇒⋆-refl b

⇒⋆-⇔ : ∀ {a b} → a ⇒⋆ b → a ⇔ b
⇒⋆-⇔ {a} {b} a⇒⋆b = b , a⇒⋆b , ⇒⋆-refl b

⇔-refl : ∀ {a} → a ⇔ a
⇔-refl {a} = a , ⇒⋆-refl a , ⇒⋆-refl a

⇔-sym : ∀ {a b} → a ⇔ b → b ⇔ a
⇔-sym (c , p , q) = c , q , p

⇔-trans : ∀ {a b c} → a ⇔ b → b ⇔ c → a ⇔ c
⇔-trans (d , a⇒⋆d , b⇒⋆d) (e , b⇒⋆e , c⇒⋆e) =
  let f , d⇒⋆f , e⇒⋆f = confluence b⇒⋆d b⇒⋆e
  in f , ⇒⋆-trans' a⇒⋆d d⇒⋆f , ⇒⋆-trans' c⇒⋆e e⇒⋆f

⇔-subst : ∀ {a b} σ → a ⇔ b → subst σ a ⇔ subst σ b
⇔-subst σ (c , a⇒⋆c , b⇒⋆c) = subst σ c , ⇒⋆-subst σ a⇒⋆c , ⇒⋆-subst σ b⇒⋆c

⇔-cong : ∀ {a a' b b'} → a ⇔ a' → b ⇔ b' → subst (a +: var) b ⇔ subst (a' +: var) b'
⇔-cong (a'' , a⇒⋆a'' , a'⇒⋆a'') (b'' , b⇒⋆b'' , b'⇒⋆b'') =
  subst (a'' +: var) b'' , ⇒⋆-cong a⇒⋆a'' b⇒⋆b'' , ⇒⋆-cong a'⇒⋆a'' b'⇒⋆b''

⇔-cong₂ : ∀ {a a' b b'} c → a ⇔ a' → b ⇔ b' → subst (a +: b +: var) c ⇔ subst (a' +: b' +: var) c
⇔-cong₂ c (a'' , a⇒⋆a'' , a'⇒⋆a'') (b'' , b⇒⋆b'' , b'⇒⋆b'') =
  subst (a'' +: b'' +: var) c , ⇒⋆-cong₂ c a⇒⋆a'' b⇒⋆b'' , ⇒⋆-cong₂ c a'⇒⋆a'' b'⇒⋆b''

⇔-Π : ∀ {aₗ aᵣ bₗ bᵣ} → aₗ ⇔ aᵣ → bₗ ⇔ bᵣ → Π aₗ bₗ ⇔ Π aᵣ bᵣ
⇔-Π (a , aₗ⇒⋆a , aᵣ⇒⋆a) (b , bₗ⇒⋆b , bᵣ⇒⋆b) = Π a b , ⇒⋆-Π aₗ⇒⋆a bₗ⇒⋆b , ⇒⋆-Π aᵣ⇒⋆a bᵣ⇒⋆b

⇔-λᵈ : ∀ {bₗ bᵣ} → bₗ ⇔ bᵣ → λᵈ bₗ ⇔ λᵈ bᵣ
⇔-λᵈ (b , bₗ⇒⋆b , bᵣ⇒⋆b) = λᵈ b , ⇒⋆-λᵈ bₗ⇒⋆b , ⇒⋆-λᵈ bᵣ⇒⋆b

⇔-$ᵈ : ∀ {aₗ aᵣ bₗ bᵣ} → bₗ ⇔ bᵣ → aₗ ⇔ aᵣ → $ᵈ bₗ aₗ ⇔ $ᵈ bᵣ aᵣ
⇔-$ᵈ (b , bₗ⇒⋆b , bᵣ⇒⋆b) (a , aₗ⇒⋆a , aᵣ⇒⋆a) = $ᵈ b a , ⇒⋆-$ᵈ bₗ⇒⋆b aₗ⇒⋆a , ⇒⋆-$ᵈ bᵣ⇒⋆b aᵣ⇒⋆a

⇔-abs : ∀ {bₗ bᵣ} → bₗ ⇔ bᵣ → abs bₗ ⇔ abs bᵣ
⇔-abs (b , bₗ⇒⋆b , bᵣ⇒⋆b) = abs b , ⇒⋆-abs bₗ⇒⋆b , ⇒⋆-abs bᵣ⇒⋆b

⇔-eq : ∀ {Aₗ Aᵣ aₗ aᵣ bₗ bᵣ} → Aₗ ⇔ Aᵣ → aₗ ⇔ aᵣ → bₗ ⇔ bᵣ → eq Aₗ aₗ bₗ ⇔ eq Aᵣ aᵣ bᵣ
⇔-eq (A , Aₗ⇒⋆A , Aᵣ⇒⋆A) (a , aₗ⇒⋆a , aᵣ⇒⋆a) (b , bₗ⇒⋆b , bᵣ⇒⋆b) = eq A a b , ⇒⋆-eq Aₗ⇒⋆A aₗ⇒⋆a bₗ⇒⋆b , ⇒⋆-eq Aᵣ⇒⋆A aᵣ⇒⋆a bᵣ⇒⋆b

⇔-J : ∀ {dₗ dᵣ pₗ pᵣ} → dₗ ⇔ dᵣ → pₗ ⇔ pᵣ → J dₗ pₗ ⇔ J dᵣ pᵣ
⇔-J (d , dₗ⇒⋆d , dᵣ⇒⋆d) (p , pₗ⇒⋆p , pᵣ⇒⋆p) = J d p , ⇒⋆-J dₗ⇒⋆d pₗ⇒⋆p , ⇒⋆-J dᵣ⇒⋆d pᵣ⇒⋆p

⇔-if : ∀ {bₗ bᵣ aₗ aᵣ cₗ cᵣ} → bₗ ⇔ bᵣ → aₗ ⇔ aᵣ → cₗ ⇔ cᵣ → if bₗ aₗ cₗ ⇔ if bᵣ aᵣ cᵣ
⇔-if (b , bₗ⇒⋆b , bᵣ⇒⋆b) (a , aₗ⇒⋆a , aᵣ⇒⋆a) (c , cₗ⇒⋆c , cᵣ⇒⋆c) = if b a c , ⇒⋆-if bₗ⇒⋆b aₗ⇒⋆a cₗ⇒⋆c , ⇒⋆-if bᵣ⇒⋆b aᵣ⇒⋆a cᵣ⇒⋆c

⇎-𝒰mty : ∀ {k} → 𝒰 k ⇔ mty → ⊥
⇎-𝒰mty (_ , 𝒰⇒⋆b , mty⇒⋆b) with ⇒⋆-𝒰-inv 𝒰⇒⋆b | ⇒⋆-mty-inv mty⇒⋆b
... | refl | ()

⇎-𝒰Π : ∀ {k a b} → 𝒰 k ⇔ Π a b → ⊥
⇎-𝒰Π (_ , 𝒰⇒⋆b , Π⇒⋆b) with ⇒⋆-𝒰-inv 𝒰⇒⋆b | ⇒⋆-Π-inv Π⇒⋆b
... | refl | ()

⇎-mtyΠ : ∀ {a b} → mty ⇔ Π a b → ⊥
⇎-mtyΠ (_ , mty⇒⋆b , Π⇒⋆b) with ⇒⋆-mty-inv mty⇒⋆b | ⇒⋆-Π-inv Π⇒⋆b
... | refl | ()

⇎-𝒰eq : ∀ {k A a b} → 𝒰 k ⇔ eq A a b → ⊥
⇎-𝒰eq (_ , 𝒰⇒⋆b , eq⇒⋆b) with ⇒⋆-𝒰-inv 𝒰⇒⋆b | ⇒⋆-eq-inv eq⇒⋆b
... | refl | ()

⇎-mtyeq : ∀ {A a b} → mty ⇔ eq A a b → ⊥
⇎-mtyeq (_ , mty⇒⋆b , eq⇒⋆b) with ⇒⋆-mty-inv mty⇒⋆b | ⇒⋆-eq-inv eq⇒⋆b
... | refl | ()

⇎-Πeq : ∀ {a b C d e} → Π a b ⇔ eq C d e → ⊥
⇎-Πeq (_ , Π⇒⋆b , eq⇒⋆b) with ⇒⋆-Π-inv Π⇒⋆b | ⇒⋆-eq-inv eq⇒⋆b
... | _ , _ , refl , _ | ()

⇎-𝒰𝔹 : ∀ {k} → 𝒰 k ⇔ 𝔹 → ⊥
⇎-𝒰𝔹 (_ , 𝒰⇒⋆b , 𝔹⇒⋆b) with ⇒⋆-𝒰-inv 𝒰⇒⋆b | ⇒⋆-𝔹-inv 𝔹⇒⋆b
... | refl | ()

⇎-mty𝔹 : mty ⇔ 𝔹 → ⊥
⇎-mty𝔹 (_ , mty⇒⋆b , 𝔹⇒⋆b) with ⇒⋆-mty-inv mty⇒⋆b | ⇒⋆-𝔹-inv 𝔹⇒⋆b
... | refl | ()

⇎-Π𝔹 : ∀ {a b} → Π a b ⇔ 𝔹 → ⊥
⇎-Π𝔹 (_ , Π⇒⋆b , 𝔹⇒⋆b) with ⇒⋆-Π-inv Π⇒⋆b | ⇒⋆-𝔹-inv 𝔹⇒⋆b
... | _ , _ , refl , _ | ()

⇎-eq𝔹 : ∀ {A a b} → eq A a b ⇔ 𝔹 → ⊥
⇎-eq𝔹 (_ , eq⇒⋆b , 𝔹⇒⋆b) with ⇒⋆-eq-inv eq⇒⋆b | ⇒⋆-𝔹-inv 𝔹⇒⋆b
... | _ , _ , _ , refl , _ | ()

⇔-𝒰-inv : ∀ {jₗ jᵣ} → 𝒰 jₗ ⇔ 𝒰 jᵣ → jₗ ≡ jᵣ
⇔-𝒰-inv (_ , 𝒰ₗ⇒⋆c , 𝒰ᵣ⇒⋆c)
  with refl ← ⇒⋆-𝒰-inv 𝒰ₗ⇒⋆c
  with refl ← ⇒⋆-𝒰-inv 𝒰ᵣ⇒⋆c = refl

⇔-Π-inv : ∀ {aₗ aᵣ bₗ bᵣ} → Π aₗ bₗ ⇔ Π aᵣ bᵣ → aₗ ⇔ aᵣ × bₗ ⇔ bᵣ
⇔-Π-inv {aₗ = aₗ} {bₗ = bₗ} (c , Πabₗ⇒⋆c , Πabᵣ⇒⋆c) =
  let aₗ' , bₗ' , pₗ , aₗ⇒⋆aₗ' , bₗ⇒⋆bₗ' = ⇒⋆-Π-inv Πabₗ⇒⋆c
      aᵣ' , bᵣ' , pᵣ , aᵣ⇒⋆aᵣ' , bᵣ⇒⋆bᵣ' = ⇒⋆-Π-inv Πabᵣ⇒⋆c
      aₗ'≡aᵣ' , bₗ'≡bᵣ' = invΠ (trans (sym pₗ) pᵣ)
  in (aᵣ' , transp (aₗ ⇒⋆_) aₗ'≡aᵣ' aₗ⇒⋆aₗ' , aᵣ⇒⋆aᵣ') ,
     (bᵣ' , transp (bₗ ⇒⋆_) bₗ'≡bᵣ' bₗ⇒⋆bₗ' , bᵣ⇒⋆bᵣ')

⇔-eq-inv : ∀ {Aₗ Aᵣ aₗ aᵣ bₗ bᵣ} → eq Aₗ aₗ bₗ ⇔ eq Aᵣ aᵣ bᵣ → Aₗ ⇔ Aᵣ × aₗ ⇔ aᵣ × bₗ ⇔ bᵣ
⇔-eq-inv {Aₗ = Aₗ} {aₗ = aₗ} {bₗ = bₗ} (c , eqₗ⇒⋆c , eqᵣ⇒⋆c) =
  let Aₗ' , aₗ' , bₗ' , pₗ , Aₗ⇒⋆Aₗ' , aₗ⇒⋆aₗ' , bₗ⇒⋆bₗ' = ⇒⋆-eq-inv eqₗ⇒⋆c
      Aᵣ' , aᵣ' , bᵣ' , pᵣ , Aᵣ⇒⋆Aᵣ' , aᵣ⇒⋆aᵣ' , bᵣ⇒⋆bᵣ' = ⇒⋆-eq-inv eqᵣ⇒⋆c
      Aₗ'≡Aᵣ' , aₗ'≡aᵣ' , bₗ'≡bᵣ' = inveq (trans (sym pₗ) pᵣ)
  in (Aᵣ' , transp (Aₗ ⇒⋆_) Aₗ'≡Aᵣ' Aₗ⇒⋆Aₗ' , Aᵣ⇒⋆Aᵣ') ,
     (aᵣ' , transp (aₗ ⇒⋆_) aₗ'≡aᵣ' aₗ⇒⋆aₗ' , aᵣ⇒⋆aᵣ') ,
     (bᵣ' , transp (bₗ ⇒⋆_) bₗ'≡bᵣ' bₗ⇒⋆bₗ' , bᵣ⇒⋆bᵣ')