open import common

module syntactics (Level : Set) where

variable
  A B C : Set
  P : A → Set

infixr 10 _+:_
_+:_ : A → (Nat → A) → Nat → A
(x +: ξ) zero = x
(x +: ξ) (suc n) = ξ n

{-----------------------
  Terms and congruence
-----------------------}

data Term : Set where
  var : Nat → Term
  𝒰 : Level → Term
  Π : Term → Term → Term
  λᵈ : Term → Term
  $ᵈ : Term → Term → Term
  mty : Term
  abs : Term → Term
  eq : Term → Term → Term → Term
  refl : Term
  J : Term → Term → Term
  𝔹 : Term
  true : Term
  false : Term
  if : Term → Term → Term → Term

congΠ : ∀ {A A' B B'} → A ≡ A' → B ≡ B' → Π A B ≡ Π A' B'
congΠ refl refl = refl

invΠ : ∀ {A A' B B'} → Π A B ≡ Π A' B' → A ≡ A' × B ≡ B'
invΠ refl = refl , refl

cong$ᵈ : ∀ {b b' a a'} → b ≡ b' → a ≡ a' → $ᵈ b a ≡ $ᵈ b' a'
cong$ᵈ refl refl = refl

congeq : ∀ {A A' a a' b b'} → A ≡ A' → a ≡ a' → b ≡ b' → eq A a b ≡ eq A' a' b'
congeq refl refl refl = refl

inveq : ∀ {A A' a a' b b'} → eq A a b ≡ eq A' a' b' → A ≡ A' × a ≡ a' × b ≡ b'
inveq refl = refl , refl , refl

congJ : ∀ {d d' p p'} → d ≡ d' → p ≡ p' → J d p ≡ J d' p'
congJ refl refl = refl

congif : ∀ {b b' a a' c c'} → b ≡ b' → a ≡ a' → c ≡ c' → if b a c ≡ if b' a' c'
congif refl refl refl = refl

{--------------------
  Lifting renamings
---------------------}

lift : (Nat → Nat) → Nat → Nat
lift ξ = 0 +: (suc ∘ ξ)

-- Lifting composes
lift∘ : ∀ ξ ζ ρ → (∀ x → (ξ ∘ ζ) x ≡ ρ x) → ∀ x → (lift ξ ∘ lift ζ) x ≡ lift ρ x
lift∘ ξ ζ ρ h zero = refl
lift∘ ξ ζ ρ h (suc n) = cong suc (h n)

{---------------------
  Applying renamings
---------------------}

rename : (Nat → Nat) → Term → Term
rename ξ (var s) = var (ξ s)
rename ξ (𝒰 k) = 𝒰 k
rename ξ (Π A B) = Π (rename ξ A) (rename (lift ξ) B)
rename ξ (λᵈ b) = λᵈ (rename (lift ξ) b)
rename ξ ($ᵈ b a) = $ᵈ (rename ξ b) (rename ξ a)
rename ξ mty = mty
rename ξ (abs b) = abs (rename ξ b)
rename ξ (eq A a b) = eq (rename ξ A) (rename ξ a) (rename ξ b)
rename ξ refl = refl
rename ξ (J d p) = J (rename ξ d) (rename ξ p)
rename ξ 𝔹 = 𝔹
rename ξ true = true
rename ξ false = false
rename ξ (if b a c) = if (rename ξ b) (rename ξ a) (rename ξ c)

-- Renamings compose
rename∘' : ∀ ξ ζ ς → (∀ x → (ξ ∘ ζ) x ≡ ς x) → ∀ s → (rename ξ ∘ rename ζ) s ≡ rename ς s
rename∘' ξ ζ ς h (var s) = cong var (h s)
rename∘' ξ ζ ς h (𝒰 k) = refl
rename∘' ξ ζ ς h (Π A B) = congΠ (rename∘' ξ ζ ς h A) (rename∘' (lift ξ) (lift ζ) (lift ς) (lift∘ ξ ζ ς h) B)
rename∘' ξ ζ ς h (λᵈ b) = cong λᵈ (rename∘' (lift ξ) (lift ζ) (lift ς) (lift∘ ξ ζ ς h) b)
rename∘' ξ ζ ς h ($ᵈ b a) = cong$ᵈ (rename∘' ξ ζ ς h b) (rename∘' ξ ζ ς h a)
rename∘' ξ ζ ς h mty = refl
rename∘' ξ ζ ς h (abs b) = cong abs (rename∘' ξ ζ ς h b)
rename∘' ξ ζ ς h (eq A a b) = congeq (rename∘' ξ ζ ς h A) (rename∘' ξ ζ ς h a) (rename∘' ξ ζ ς h b)
rename∘' ξ ζ ς h refl = refl
rename∘' ξ ζ ς h (J d p) = congJ (rename∘' ξ ζ ς h d) (rename∘' ξ ζ ς h p)
rename∘' ξ ζ ς h 𝔹 = refl
rename∘' ξ ζ ς h true = refl
rename∘' ξ ζ ς h false = refl
rename∘' ξ ζ ς h (if b a c) = congif (rename∘' ξ ζ ς h b) (rename∘' ξ ζ ς h a) (rename∘' ξ ζ ς h c)

rename∘ : ∀ ξ ζ → ∀ s → (rename ξ ∘ rename ζ) s ≡ rename (ξ ∘ ζ) s
rename∘ ξ ζ s = rename∘' ξ ζ (ξ ∘ ζ) (λ _ → refl) s

-- Push renaming into single substitution
renameLift : ∀ ξ a s → (rename ξ ∘ (a +: var)) s ≡ ((rename ξ a +: var) ∘ lift ξ) s
renameLift ξ a zero = refl
renameLift ξ a (suc n) = refl

{------------------------
  Lifting substitutions
------------------------}

infix 30 ↑_
↑_ : (Nat → Term) → Nat → Term
↑ σ = var 0 +: (rename suc ∘ σ)

-- Lifting twice pushes renamings inwards
↑↑ : ∀ σ x → (↑ ↑ σ) x ≡ (var 0 +: var 1 +: (rename suc ∘ rename suc ∘ σ)) x
↑↑ σ zero = refl
↑↑ σ (suc zero) = refl
↑↑ σ (suc (suc n)) = refl

-- Lifting var "substitution" does nothing
↑id : ∀ σ → (∀ x → σ x ≡ var x) → ∀ x → (↑ σ) x ≡ var x
↑id σ h zero = refl
↑id σ h (suc n) = cong (rename suc) (h n)

-- Lifting respects substitution extensionality
↑ext : ∀ σ τ → (∀ x → σ x ≡ τ x) → ∀ x → (↑ σ) x ≡ (↑ τ) x
↑ext σ τ h zero = refl
↑ext σ τ h (suc n) = cong (rename suc) (h n)

-- Lifting commutes with composition
↑lift : ∀ ξ σ τ → (∀ x → (σ ∘ ξ) x ≡ τ x) → ∀ x → (↑ σ ∘ lift ξ) x ≡ (↑ τ) x
↑lift ξ σ τ h zero = refl
↑lift ξ σ τ h (suc n) = cong (rename suc) (h n)

-- Lifting commutes with renaming
↑rename : ∀ ξ σ τ → (∀ x → (rename ξ ∘ σ) x ≡ τ x) → ∀ x → (rename (lift ξ) ∘ ↑ σ) x ≡ (↑ τ) x
↑rename ξ σ τ h zero = refl
↑rename ξ σ τ h (suc n) = begin
  (rename (lift ξ) ∘ rename suc) (σ n) ≡⟨ rename∘ (lift ξ) suc (σ n) ⟩
  rename (lift ξ ∘ suc) (σ n)          ≡⟨⟩
  (rename (suc ∘ ξ)) (σ n)             ≡⟨ sym (rename∘ suc ξ (σ n)) ⟩
  (rename suc ∘ rename ξ) (σ n)        ≡⟨⟩
  rename suc ((rename ξ ∘ σ) n)        ≡⟨ cong (rename suc) (h n) ⟩
  rename suc (τ n) ∎

{-------------------------
  Applying substitutions
-------------------------}

subst : (Nat → Term) → Term → Term
subst σ (var s) = σ s
subst σ (𝒰 k) = 𝒰 k
subst σ (Π A B) = Π (subst σ A) (subst (↑ σ) B)
subst σ (λᵈ b) = λᵈ (subst (↑ σ) b)
subst σ ($ᵈ b a) = $ᵈ (subst σ b) (subst σ a)
subst σ mty = mty
subst σ (abs b) = abs (subst σ b)
subst σ (eq A a b) = eq (subst σ A) (subst σ a) (subst σ b)
subst σ refl = refl
subst σ (J d p) = J (subst σ d) (subst σ p)
subst σ 𝔹 = 𝔹
subst σ true = true
subst σ false = false
subst σ (if b a c) = if (subst σ b) (subst σ a) (subst σ c)

-- Substitution extensionality
substExt : ∀ σ τ → (∀ x → σ x ≡ τ x) → ∀ s → subst σ s ≡ subst τ s
substExt σ τ h (var s) = h s
substExt σ τ h (𝒰 k) = refl
substExt σ τ h (Π A B) = congΠ (substExt σ τ h A) (substExt (↑ σ) (↑ τ) (↑ext σ τ h) B)
substExt σ τ h (λᵈ b) = cong λᵈ (substExt (↑ σ) (↑ τ) (↑ext σ τ h) b)
substExt σ τ h ($ᵈ b a) = cong$ᵈ (substExt σ τ h b) (substExt σ τ h a)
substExt σ τ h mty = refl
substExt σ τ h (abs b) = cong abs (substExt σ τ h b)
substExt σ τ h (eq A a b) = congeq (substExt σ τ h A) (substExt σ τ h a) (substExt σ τ h b)
substExt σ τ h refl = refl
substExt σ τ h (J d p) = congJ (substExt σ τ h d) (substExt σ τ h p)
substExt σ τ h 𝔹 = refl
substExt σ τ h true = refl
substExt σ τ h false = refl
substExt σ τ h (if b a c) = congif (substExt σ τ h b) (substExt σ τ h a) (substExt σ τ h c)

-- Applying var "substitution" does nothing
substId' : ∀ σ → (∀ x → σ x ≡ var x) → ∀ s → subst σ s ≡ s
substId' σ h (var s) = h s
substId' σ h (𝒰 k) = refl
substId' σ h (Π A B) = congΠ (substId' σ h A) (substId' (↑ σ) (↑id σ h) B)
substId' σ h (λᵈ b) = cong λᵈ (substId' (↑ σ) (↑id σ h) b)
substId' σ h ($ᵈ b a) = cong$ᵈ (substId' σ h b) (substId' σ h a)
substId' σ h mty = refl
substId' σ h (abs b) = cong abs (substId' σ h b)
substId' σ h (eq A a b) = congeq (substId' σ h A) (substId' σ h a) (substId' σ h b)
substId' σ h refl = refl
substId' σ h (J d p) = congJ (substId' σ h d) (substId' σ h p)
substId' σ h 𝔹 = refl
substId' σ h true = refl
substId' σ h false = refl
substId' σ h (if b a c) = congif (substId' σ h b) (substId' σ h a) (substId' σ h c)

-- Substitution/renaming compositionality
substRename' : ∀ ξ (σ τ : Nat → Term) → (∀ x → (σ ∘ ξ) x ≡ τ x) → ∀ s → subst σ (rename ξ s) ≡ subst τ s
substRename' ξ σ τ h (var s) = h s
substRename' ξ σ τ h (𝒰 k) = refl
substRename' ξ σ τ h (Π A B) = congΠ (substRename' ξ σ τ h A) (substRename' (lift ξ) (↑ σ) (↑ τ) (↑lift ξ σ τ h) B)
substRename' ξ σ τ h (λᵈ b) = cong λᵈ (substRename' (lift ξ) (↑ σ) (↑ τ) (↑lift ξ σ τ h) b)
substRename' ξ σ τ h ($ᵈ b a) = cong$ᵈ (substRename' ξ σ τ h b) (substRename' ξ σ τ h a)
substRename' ξ σ τ h mty = refl
substRename' ξ σ τ h (abs b) = cong abs (substRename' ξ σ τ h b)
substRename' ξ σ τ h (eq A a b) = congeq (substRename' ξ σ τ h A) (substRename' ξ σ τ h a) (substRename' ξ σ τ h b)
substRename' ξ σ τ h refl = refl
substRename' ξ σ τ h (J d p) = congJ (substRename' ξ σ τ h d) (substRename' ξ σ τ h p)
substRename' ξ σ τ h 𝔹 = refl
substRename' ξ σ τ h true = refl
substRename' ξ σ τ h false = refl
substRename' ξ σ τ h (if b a c) = congif (substRename' ξ σ τ h b) (substRename' ξ σ τ h a) (substRename' ξ σ τ h c)

-- Renaming/substitution compositionality
renameSubst' : ∀ ξ σ τ → (∀ x → (rename ξ ∘ σ) x ≡ τ x) → ∀ s → rename ξ (subst σ s) ≡ subst τ s
renameSubst' ξ σ τ h (var s) = h s
renameSubst' ξ σ τ h (𝒰 k) = refl
renameSubst' ξ σ τ h (Π A B) = congΠ (renameSubst' ξ σ τ h A) (renameSubst' (lift ξ) (↑ σ) (↑ τ) (↑rename ξ σ τ h) B)
renameSubst' ξ σ τ h (λᵈ b) = cong λᵈ (renameSubst' (lift ξ) (↑ σ) (↑ τ) (↑rename ξ σ τ h) b)
renameSubst' ξ σ τ h ($ᵈ b a) = cong$ᵈ (renameSubst' ξ σ τ h b) (renameSubst' ξ σ τ h a)
renameSubst' ξ σ τ h mty = refl
renameSubst' ξ σ τ h (abs b) = cong abs (renameSubst' ξ σ τ h b)
renameSubst' ξ σ τ h (eq A a b) = congeq (renameSubst' ξ σ τ h A) (renameSubst' ξ σ τ h a) (renameSubst' ξ σ τ h b)
renameSubst' ξ σ τ h refl = refl
renameSubst' ξ σ τ h (J d p) = congJ (renameSubst' ξ σ τ h d) (renameSubst' ξ σ τ h p)
renameSubst' ξ σ τ h 𝔹 = refl
renameSubst' ξ σ τ h true = refl
renameSubst' ξ σ τ h false = refl
renameSubst' ξ σ τ h (if b a c) = congif (renameSubst' ξ σ τ h b) (renameSubst' ξ σ τ h a) (renameSubst' ξ σ τ h c)

-- Lifting commutes with substitution
↑subst : ∀ ρ σ τ → (∀ x → (subst ρ ∘ σ) x ≡ τ x) → ∀ x → (subst (↑ ρ) ∘ (↑ σ)) x ≡ (↑ τ) x
↑subst ρ σ τ h zero = refl
↑subst ρ σ τ h (suc n) = begin
  (subst (↑ ρ) ∘ rename suc) (σ n) ≡⟨ substRename' suc (↑ ρ) (↑ ρ ∘ suc) (λ _ → refl) (σ n) ⟩
  subst (↑ ρ ∘ suc) (σ n)          ≡⟨⟩
  subst (rename suc ∘ ρ) (σ n)     ≡⟨ sym (renameSubst' suc ρ (rename suc ∘ ρ) (λ _ → refl) (σ n)) ⟩
  (rename suc ∘ subst ρ) (σ n)     ≡⟨⟩
  rename suc (subst ρ (σ n))       ≡⟨ cong (rename suc) (h n) ⟩
  rename suc (τ n) ∎

-- Substitution compositionality
subst∘' : ∀ ρ σ τ → (∀ x → (subst ρ ∘ σ) x ≡ τ x) → ∀ s → (subst ρ ∘ subst σ) s ≡ subst τ s
subst∘' ρ σ τ h (var s) = h s
subst∘' ρ σ τ h (𝒰 k) = refl
subst∘' ρ σ τ h (Π A B) = congΠ (subst∘' ρ σ τ h A) (subst∘' (↑ ρ) (↑ σ) (↑ τ) (↑subst ρ σ τ h) B)
subst∘' ρ σ τ h (λᵈ b) = cong λᵈ (subst∘' (↑ ρ) (↑ σ) (↑ τ) (↑subst ρ σ τ h) b)
subst∘' ρ σ τ h ($ᵈ b a) = cong$ᵈ (subst∘' ρ σ τ h b) (subst∘' ρ σ τ h a)
subst∘' ρ σ τ h mty = refl
subst∘' ρ σ τ h (abs b) = cong abs (subst∘' ρ σ τ h b)
subst∘' ρ σ τ h (eq A a b) = congeq (subst∘' ρ σ τ h A) (subst∘' ρ σ τ h a) (subst∘' ρ σ τ h b)
subst∘' ρ σ τ h refl = refl
subst∘' ρ σ τ h (J d p) = congJ (subst∘' ρ σ τ h d) (subst∘' ρ σ τ h p)
subst∘' ρ σ τ h 𝔹 = refl
subst∘' ρ σ τ h true = refl
subst∘' ρ σ τ h false = refl
subst∘' ρ σ τ h (if b a c) = congif (subst∘' ρ σ τ h b) (subst∘' ρ σ τ h a) (subst∘' ρ σ τ h c)

{------------------------------------------------
  Substitution & renaming lemmas, extensionally
------------------------------------------------}

substId : ∀ s → subst var s ≡ s
substId = substId' var (λ _ → refl)

substRename : ∀ ξ σ s → (subst σ ∘ rename ξ) s ≡ subst (σ ∘ ξ) s
substRename ξ σ = substRename' ξ σ (σ ∘ ξ) (λ _ → refl)

renameSubst : ∀ ξ σ s → (rename ξ ∘ subst σ) s ≡ subst (rename ξ ∘ σ) s
renameSubst ξ σ = renameSubst' ξ σ (rename ξ ∘ σ) (λ _ → refl)

subst∘ : ∀ σ τ s → (subst σ ∘ subst τ) s ≡ subst (subst σ ∘ τ) s
subst∘ σ τ = subst∘' σ τ (subst σ ∘ τ) (λ _ → refl)

{---------------------------------------------------
  Handy dandy derived renaming substitution lemmas
---------------------------------------------------}

renameDist : ∀ ξ a s → subst (rename ξ a +: var) (rename (lift ξ) s) ≡ rename ξ (subst (a +: var) s)
renameDist ξ a s = begin
  subst (rename ξ a +: var) (rename (lift ξ) s) ≡⟨ substRename (lift ξ) (rename ξ a +: var) s ⟩
  subst ((rename ξ a +: var) ∘ (lift ξ)) s      ≡⟨ sym (substExt _ _ (renameLift ξ a) s) ⟩
  subst (rename ξ ∘ (a +: var)) s               ≡⟨ sym (renameSubst ξ (a +: var) s) ⟩
  rename ξ (subst (a +: var) s) ∎

substDrop : ∀ (σ : Nat → Term) a n → σ n ≡ subst (a +: var) (rename suc (σ n))
substDrop σ a n = begin
  σ n             ≡⟨ sym (substId (σ n)) ⟩
  subst var (σ n) ≡⟨ sym (substRename suc (a +: var) (σ n)) ⟩
  subst (a +: var) (rename suc (σ n)) ∎

substDrop₂ : ∀ (σ : Nat → Term) a b n → σ n ≡ subst (a +: b +: var) (rename suc (rename suc (σ n)))
substDrop₂ σ a b n = begin
  σ n                                              ≡⟨ sym (substId (σ n)) ⟩
  subst var (σ n)                                  ≡⟨ sym (substRename (suc ∘ suc) (a +: b +: var) (σ n)) ⟩
  subst (a +: b +: var) (rename (suc ∘ suc) (σ n)) ≡⟨ cong (subst (a +: b +: var)) (sym (rename∘ suc suc (σ n))) ⟩
  subst (a +: b +: var) (rename suc (rename suc (σ n))) ∎

substUnion : ∀ σ a s → subst (a +: σ) s ≡ subst (a +: var) (subst (↑ σ) s)
substUnion σ a s = begin
  subst (a +: σ) s                                         ≡⟨ substExt _ _ (λ {zero → refl ; (suc n) → substDrop σ a n}) s ⟩
  subst (subst (a +: var) ∘ (var 0 +: (rename suc ∘ σ))) s ≡⟨ sym (subst∘ (a +: var) (↑ σ) s) ⟩
  (subst (a +: var) ∘ subst (var 0 +: (rename suc ∘ σ))) s ∎

substUnion₂ : ∀ σ a b s → subst (a +: b +: σ) s ≡ subst (a +: b +: var) (subst (↑ ↑ σ) s)
substUnion₂ σ a b s = begin
  subst (a +: b +: σ) s
    ≡⟨ substExt _ _ (λ {zero → refl ; (suc zero) → refl ; (suc (suc n)) → substDrop₂ σ a b n}) s ⟩
  subst (subst (a +: b +: var) ∘ (var 0 +: var 1 +: (rename suc ∘ rename suc ∘ σ))) s
    ≡⟨ sym (subst∘ (a +: b +: var) (var 0 +: var 1 +: (rename suc ∘ rename suc ∘ σ)) s) ⟩
  (subst (a +: b +: var) ∘ subst (var 0 +: var 1 +: (rename suc ∘ rename suc ∘ σ))) s
    ≡⟨ cong (subst (a +: b +: var)) (sym (substExt _ _ (↑↑ σ) s)) ⟩
  (subst (a +: b +: var) ∘ subst (↑ ↑ σ)) s ∎

substDist : ∀ σ a s → subst (subst σ a +: var) (subst (↑ σ) s) ≡ subst σ (subst (a +: var) s)
substDist σ a s = begin
  (subst (subst σ a +: var) ∘ subst (↑ σ)) s ≡⟨ sym (substUnion σ (subst σ a) s) ⟩
  subst (subst σ a +: σ) s                   ≡⟨ substExt _ _ (λ {zero → refl ; (suc n) → refl}) s ⟩
  subst (subst σ ∘ (a +: var)) s             ≡⟨ sym (subst∘ σ (a +: var) s) ⟩
  (subst σ ∘ subst (a +: var)) s ∎

substDist₂ : ∀ σ a b s → subst (subst σ a +: subst σ b +: var) (subst (↑ ↑ σ) s) ≡ subst σ (subst (a +: b +: var) s)
substDist₂ σ a b s = begin
  subst (subst σ a +: subst σ b +: var) (subst (↑ ↑ σ) s) ≡⟨ sym (substUnion₂ σ (subst σ a) (subst σ b) s) ⟩
  subst (subst σ a +: subst σ b +: σ) s                   ≡⟨ substExt _ _ (λ {zero → refl ; (suc zero) → refl ; (suc (suc n)) → refl}) s ⟩
  subst (subst σ ∘ a +: b +: var) s                       ≡⟨ sym (subst∘ σ (a +: b +: var) s) ⟩
  (subst σ ∘ subst (a +: b +: var)) s ∎

{--------------------------
  Contexts and membership
--------------------------}
infixl 30 _∷_
data Ctxt : Set where
  ∙ : Ctxt
  _∷_ : Ctxt → Term → Ctxt

infix 40 _⦂_∈_
data _⦂_∈_ : Nat → Term → Ctxt → Set where
  here  : ∀ {Γ A} → 0 ⦂ (rename suc A) ∈ (Γ ∷ A)
  there : ∀ {Γ x A B} → x ⦂ A ∈ Γ → suc x ⦂ (rename suc A) ∈ (Γ ∷ B)