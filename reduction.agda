open import common
import syntactics

module reduction (Level : Set) where
open syntactics Level

{---------------------
  Parallel reduction
---------------------}

data _⇒_ : Term → Term → Set where
  ⇒-β   : ∀ {b b' a a'} →
          b ⇒ b' →
          a ⇒ a' →
          ----------------------------------
          $ᵈ (λᵈ b) a ⇒ subst (a' +: var) b'
  ⇒-var : ∀ s → var s ⇒ var s
  ⇒-∗   : ∗ ⇒ ∗
  ⇒-Π   : ∀ {a a' j b b'} →
          a ⇒ a' →
          b ⇒ b' →
          -------------------
          Π a j b ⇒ Π a' j b'
  ⇒-λᵈ  : ∀ {b b'} →
          b ⇒ b' →
          ------------
          λᵈ b ⇒ λᵈ b'
  ⇒-$ᵈ  : ∀ {b b' a a'} →
          b ⇒ b' →
          a ⇒ a' →
          -----------------
          $ᵈ b a ⇒ $ᵈ b' a'
  ⇒-mty : mty ⇒ mty
  ⇒-abs : ∀ {b b'} →
          b ⇒ b' →
          --------------
          abs b ⇒ abs b'

⇒-refl : ∀ a → a ⇒ a
⇒-refl (var s) = ⇒-var s
⇒-refl ∗ = ⇒-∗
⇒-refl (Π a _ b) = ⇒-Π (⇒-refl a) (⇒-refl b)
⇒-refl (λᵈ b) = ⇒-λᵈ (⇒-refl b)
⇒-refl ($ᵈ b a) = ⇒-$ᵈ (⇒-refl b) (⇒-refl a)
⇒-refl mty = ⇒-mty
⇒-refl (abs b) = ⇒-abs (⇒-refl b)

⇒-rename : ∀ {a b} ξ → a ⇒ b → rename ξ a ⇒ rename ξ b
⇒-rename ξ (⇒-β {b} {b'} {a} {a'} b⇒b' a⇒a') =
  transp (_ ⇒_) (renameDist ξ a' b') h where
  h : $ᵈ (λᵈ (rename (lift ξ) b)) (rename ξ a) ⇒ subst (rename ξ a' +: var) (rename (lift ξ) b')
  h = ⇒-β (⇒-rename (lift ξ) b⇒b') (⇒-rename ξ a⇒a')
⇒-rename ξ (⇒-var s) = ⇒-var (ξ s)
⇒-rename ξ ⇒-∗ = ⇒-∗
⇒-rename ξ (⇒-Π a⇒a' b⇒b') = ⇒-Π (⇒-rename ξ a⇒a') (⇒-rename (lift ξ) b⇒b')
⇒-rename ξ (⇒-λᵈ b⇒b') = ⇒-λᵈ (⇒-rename (lift ξ) b⇒b')
⇒-rename ξ (⇒-$ᵈ b⇒b' a⇒a') = ⇒-$ᵈ (⇒-rename ξ b⇒b') (⇒-rename ξ a⇒a')
⇒-rename ξ ⇒-mty = ⇒-mty
⇒-rename ξ (⇒-abs b⇒b') = ⇒-abs (⇒-rename ξ b⇒b')

⇒-lift : ∀ {σ τ} → (∀ x → σ x ⇒ τ x) → ∀ x → (↑ σ) x ⇒ (↑ τ) x
⇒-lift r zero = ⇒-var 0
⇒-lift r (suc n) = ⇒-rename suc (r n)

⇒-morphing : ∀ {a b} σ τ → (∀ x → σ x ⇒ τ x) → a ⇒ b → subst σ a ⇒ subst τ b
⇒-morphing σ τ r (⇒-β {b} {b'} {a} {a'} b⇒b' a⇒a') =
  transp (subst σ ($ᵈ (λᵈ b) a) ⇒_) (substDist τ a' b') h where
  h : $ᵈ (λᵈ (subst (↑ σ) b)) (subst σ a) ⇒ subst (subst τ a' +: var) (subst (↑ τ) b')
  h = ⇒-β (⇒-morphing (↑ σ) (↑ τ) (⇒-lift r) b⇒b') (⇒-morphing σ τ r a⇒a')
⇒-morphing σ τ r (⇒-var s) = r s
⇒-morphing σ τ r ⇒-∗ = ⇒-∗
⇒-morphing σ τ r (⇒-Π a⇒a' b⇒b') = ⇒-Π (⇒-morphing σ τ r a⇒a') (⇒-morphing (↑ σ) (↑ τ) (⇒-lift r) b⇒b')
⇒-morphing σ τ r (⇒-λᵈ b⇒b') = ⇒-λᵈ (⇒-morphing (↑ σ) (↑ τ) (⇒-lift r) b⇒b')
⇒-morphing σ τ r (⇒-$ᵈ b⇒b' a⇒a') = ⇒-$ᵈ (⇒-morphing σ τ r b⇒b') (⇒-morphing σ τ r a⇒a')
⇒-morphing σ τ r ⇒-mty = ⇒-mty
⇒-morphing σ τ r (⇒-abs b⇒b') = ⇒-abs (⇒-morphing σ τ r b⇒b')

⇒-subst : ∀ {a b} σ → a ⇒ b → subst σ a ⇒ subst σ b
⇒-subst σ r = ⇒-morphing σ σ (λ x → ⇒-refl (σ x)) r

⇒-cong : ∀ {a a' b b'} → a ⇒ a' → b ⇒ b' → subst (a +: var) b ⇒ subst (a' +: var) b'
⇒-cong {a} {a'} a⇒a' b⇒b' = ⇒-morphing (a +: var) (a' +: var) (λ {zero → a⇒a' ; (suc n) → ⇒-var n}) b⇒b'

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

⇒⋆-Π : ∀ {a a' j b b'} → a ⇒⋆ a' → b ⇒⋆ b' → Π a j b ⇒⋆ Π a' j b'
⇒⋆-Π (⇒⋆-refl a) (⇒⋆-refl b) = ⇒⋆-refl (Π a _ b)
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

⇒⋆-∗-inv : ∀ {b} → ∗ ⇒⋆ b → b ≡ ∗
⇒⋆-∗-inv (⇒⋆-refl ∗) = refl
⇒⋆-∗-inv (⇒⋆-trans ⇒-∗ ∗⇒⋆b) = ⇒⋆-∗-inv ∗⇒⋆b

⇒⋆-mty-inv : ∀ {b} → mty ⇒⋆ b → b ≡ mty
⇒⋆-mty-inv (⇒⋆-refl mty) = refl
⇒⋆-mty-inv (⇒⋆-trans ⇒-mty mty⇒⋆b) = ⇒⋆-mty-inv mty⇒⋆b

⇒⋆-Π-inv : ∀ {a j b c} → Π a j b ⇒⋆ c → ∃[ a' ] ∃[ b' ] c ≡ Π a' j b' × a ⇒⋆ a' × b ⇒⋆ b'
⇒⋆-Π-inv (⇒⋆-refl (Π a j b)) = a , b , refl , ⇒⋆-refl a , ⇒⋆-refl b
⇒⋆-Π-inv (⇒⋆-trans (⇒-Π a⇒a' b⇒b') Πab'⇒⋆c) =
  let a'' , b'' , p , a'⇒⋆a'' , b'⇒⋆b'' = ⇒⋆-Π-inv Πab'⇒⋆c
  in a'' , b'' , p , ⇒⋆-trans a⇒a' a'⇒⋆a'' , ⇒⋆-trans b⇒b' b'⇒⋆b''

⇒⋆-β : ∀ σ b a → ($ᵈ (λᵈ (subst (↑ σ) b)) a) ⇒⋆ (subst (a +: σ) b)
⇒⋆-β σ b a = ⇒⋆-trans (⇒-β (⇒-refl _) (⇒-refl _))
                      (transp (_⇒⋆ subst (a +: σ) b) (substUnion σ a b) (⇒⋆-refl _))

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
diamond (⇒-var s) (⇒-var s) = var s , ⇒-var s , ⇒-var s
diamond ⇒-∗ ⇒-∗ = ∗ , ⇒-∗ , ⇒-∗
diamond (⇒-Π {j = j} a⇒a₁ b⇒b₁) (⇒-Π a⇒a₂ b⇒b₂) =
  let a' , a₁⇒a' , a₂⇒a' = diamond a⇒a₁ a⇒a₂
      b' , b₁⇒b' , b₂⇒b' = diamond b⇒b₁ b⇒b₂
  in Π a' j b' , ⇒-Π a₁⇒a' b₁⇒b' , ⇒-Π a₂⇒a' b₂⇒b'
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

⇔-Π : ∀ {aₗ aᵣ j bₗ bᵣ} → aₗ ⇔ aᵣ → bₗ ⇔ bᵣ → Π aₗ j bₗ ⇔ Π aᵣ j bᵣ
⇔-Π (a , aₗ⇒⋆a , aᵣ⇒⋆a) (b , bₗ⇒⋆b , bᵣ⇒⋆b) = Π a _ b , ⇒⋆-Π aₗ⇒⋆a bₗ⇒⋆b , ⇒⋆-Π aᵣ⇒⋆a bᵣ⇒⋆b

⇔-λᵈ : ∀ {bₗ bᵣ} → bₗ ⇔ bᵣ → λᵈ bₗ ⇔ λᵈ bᵣ
⇔-λᵈ (b , bₗ⇒⋆b , bᵣ⇒⋆b) = λᵈ b , ⇒⋆-λᵈ bₗ⇒⋆b , ⇒⋆-λᵈ bᵣ⇒⋆b

⇔-$ᵈ : ∀ {aₗ aᵣ bₗ bᵣ} → bₗ ⇔ bᵣ → aₗ ⇔ aᵣ → $ᵈ bₗ aₗ ⇔ $ᵈ bᵣ aᵣ
⇔-$ᵈ (b , bₗ⇒⋆b , bᵣ⇒⋆b) (a , aₗ⇒⋆a , aᵣ⇒⋆a) = $ᵈ b a , ⇒⋆-$ᵈ bₗ⇒⋆b aₗ⇒⋆a , ⇒⋆-$ᵈ bᵣ⇒⋆b aᵣ⇒⋆a

⇔-abs : ∀ {bₗ bᵣ} → bₗ ⇔ bᵣ → abs bₗ ⇔ abs bᵣ
⇔-abs (b , bₗ⇒⋆b , bᵣ⇒⋆b) = abs b , ⇒⋆-abs bₗ⇒⋆b , ⇒⋆-abs bᵣ⇒⋆b

⇎⋆-∗mty : ∗ ⇔ mty → ⊥
⇎⋆-∗mty (b , ∗⇒⋆b , mty⇒⋆b) with ⇒⋆-∗-inv ∗⇒⋆b | ⇒⋆-mty-inv mty⇒⋆b
... | refl | ()

⇎⋆-∗Π : ∀ {a j b} → ∗ ⇔ Π a j b → ⊥
⇎⋆-∗Π (b , ∗⇒⋆b , Π⇒⋆b) with ⇒⋆-∗-inv ∗⇒⋆b | ⇒⋆-Π-inv Π⇒⋆b
... | refl | ()

⇎⋆-mtyΠ : ∀ {a j b} → mty ⇔ Π a j b → ⊥
⇎⋆-mtyΠ (b , mty⇒⋆b , Π⇒⋆b) with ⇒⋆-mty-inv mty⇒⋆b | ⇒⋆-Π-inv Π⇒⋆b
... | refl | ()

⇔-Π-inv : ∀ {aₗ aᵣ jₗ jᵣ bₗ bᵣ} → Π aₗ jₗ bₗ ⇔ Π aᵣ jᵣ bᵣ → aₗ ⇔ aᵣ × jₗ ≡ jᵣ × bₗ ⇔ bᵣ
⇔-Π-inv {aₗ = aₗ} {bₗ = bₗ} (c , Πajbₗ⇒⋆c , Πajbᵣ⇒⋆c) =
  let aₗ' , bₗ' , pₗ , aₗ⇒⋆aₗ' , bₗ⇒⋆bₗ' = ⇒⋆-Π-inv Πajbₗ⇒⋆c
      aᵣ' , bᵣ' , pᵣ , aᵣ⇒⋆aᵣ' , bᵣ⇒⋆bᵣ' = ⇒⋆-Π-inv Πajbᵣ⇒⋆c
      aₗ'≡aᵣ' , jₗ≡jᵣ , bₗ'≡bᵣ' = invΠ (trans (sym pₗ) pᵣ)
  in (aᵣ' , transp (aₗ ⇒⋆_) aₗ'≡aᵣ' aₗ⇒⋆aₗ' , aᵣ⇒⋆aᵣ') ,
     jₗ≡jᵣ ,
     (bᵣ' , transp (bₗ ⇒⋆_) bₗ'≡bᵣ' bₗ⇒⋆bₗ' , bᵣ⇒⋆bᵣ')