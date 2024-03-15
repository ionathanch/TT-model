open import common

module syntactics (Level : Set) where

variable
  A B C : Set
  P : A → Set

infix 10 _+:_
_+:_ : A → (Nat → A) → Nat → A
(x +: ξ) zero = x
(x +: ξ) (suc n) = ξ n

{-----------------------
  Terms and congruence
-----------------------}

data Term : Set where
  var : Nat → Term
  ∗ : Term
  Π : Term → Level → Term → Term
  λᵈ : Term → Term
  $ᵈ : Term → Term → Term
  mty : Term
  abs : Term → Term

congΠ : ∀ {A A' j j' B B'} → A ≡ A' → j ≡ j' → B ≡ B' → Π A j B ≡ Π A' j' B'
congΠ refl refl refl = refl

invΠ : ∀ {A A' j j' B B'} → Π A j B ≡ Π A' j' B' → A ≡ A' × j ≡ j' × B ≡ B'
invΠ refl = refl , refl , refl

cong$ᵈ : ∀ {b b' a a'} → b ≡ b' → a ≡ a' → $ᵈ b a ≡ $ᵈ b' a'
cong$ᵈ refl refl = refl

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
rename ξ ∗ = ∗
rename ξ (Π A j B) = Π (rename ξ A) j (rename (lift ξ) B)
rename ξ (λᵈ b) = λᵈ (rename (lift ξ) b)
rename ξ ($ᵈ b a) = $ᵈ (rename ξ b) (rename ξ a)
rename ξ mty = mty
rename ξ (abs b) = abs (rename ξ b)

-- Renamings compose
rename∘' : ∀ ξ ζ ς → (∀ x → (ξ ∘ ζ) x ≡ ς x) → ∀ s → (rename ξ ∘ rename ζ) s ≡ rename ς s
rename∘' ξ ζ ς h (var s) = cong var (h s)
rename∘' ξ ζ ς h ∗ = refl
rename∘' ξ ζ ς h (Π A j B) = congΠ (rename∘' ξ ζ ς h A) refl (rename∘' (lift ξ) (lift ζ) (lift ς) (lift∘ ξ ζ ς h) B)
rename∘' ξ ζ ς h (λᵈ b) = cong λᵈ (rename∘' (lift ξ) (lift ζ) (lift ς) (lift∘ ξ ζ ς h) b)
rename∘' ξ ζ ς h ($ᵈ b a) = cong$ᵈ (rename∘' ξ ζ ς h b) (rename∘' ξ ζ ς h a)
rename∘' ξ ζ ς h mty = refl
rename∘' ξ ζ ς h (abs b) = cong abs (rename∘' ξ ζ ς h b)

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
subst σ ∗ = ∗
subst σ (Π A j B) = Π (subst σ A) j (subst (↑ σ) B)
subst σ (λᵈ b) = λᵈ (subst (↑ σ) b)
subst σ ($ᵈ b a) = $ᵈ (subst σ b) (subst σ a)
subst σ mty = mty
subst σ (abs b) = abs (subst σ b)

-- Substitution extensionality
substExt : ∀ σ τ → (∀ x → σ x ≡ τ x) → ∀ s → subst σ s ≡ subst τ s
substExt σ τ h (var s) = h s
substExt σ τ h ∗ = refl
substExt σ τ h (Π A j B) = congΠ (substExt σ τ h A) refl (substExt (↑ σ) (↑ τ) (↑ext σ τ h) B)
substExt σ τ h (λᵈ b) = cong λᵈ (substExt (↑ σ) (↑ τ) (↑ext σ τ h) b)
substExt σ τ h ($ᵈ b a) = cong$ᵈ (substExt σ τ h b) (substExt σ τ h a)
substExt σ τ h mty = refl
substExt σ τ h (abs b) = cong abs (substExt σ τ h b)

-- Applying var "substitution" does nothing
substId' : ∀ σ → (∀ x → σ x ≡ var x) → ∀ s → subst σ s ≡ s
substId' σ h (var s) = h s
substId' σ h ∗ = refl
substId' σ h (Π A j B) = congΠ (substId' σ h A) refl (substId' (↑ σ) (↑id σ h) B)
substId' σ h (λᵈ b) = cong λᵈ (substId' (↑ σ) (↑id σ h) b)
substId' σ h ($ᵈ b a) = cong$ᵈ (substId' σ h b) (substId' σ h a)
substId' σ h mty = refl
substId' σ h (abs b) = cong abs (substId' σ h b)

-- Substitution/renaming compositionality
substRename' : ∀ ξ (σ τ : Nat → Term) → (∀ x → (σ ∘ ξ) x ≡ τ x) → ∀ s → subst σ (rename ξ s) ≡ subst τ s
substRename' ξ σ τ h (var s) = h s
substRename' ξ σ τ h ∗ = refl
substRename' ξ σ τ h (Π A j B) = congΠ (substRename' ξ σ τ h A) refl (substRename' (lift ξ) (↑ σ) (↑ τ) (↑lift ξ σ τ h) B)
substRename' ξ σ τ h (λᵈ b) = cong λᵈ (substRename' (lift ξ) (↑ σ) (↑ τ) (↑lift ξ σ τ h) b)
substRename' ξ σ τ h ($ᵈ b a) = cong$ᵈ (substRename' ξ σ τ h b) (substRename' ξ σ τ h a)
substRename' ξ σ τ h mty = refl
substRename' ξ σ τ h (abs b) = cong abs (substRename' ξ σ τ h b)

-- Renaming/substitution compositionality
renameSubst' : ∀ ξ σ τ → (∀ x → (rename ξ ∘ σ) x ≡ τ x) → ∀ s → rename ξ (subst σ s) ≡ subst τ s
renameSubst' ξ σ τ h (var s) = h s
renameSubst' ξ σ τ h ∗ = refl
renameSubst' ξ σ τ h (Π A j B) = congΠ (renameSubst' ξ σ τ h A) refl (renameSubst' (lift ξ) (↑ σ) (↑ τ) (↑rename ξ σ τ h) B)
renameSubst' ξ σ τ h (λᵈ b) = cong λᵈ (renameSubst' (lift ξ) (↑ σ) (↑ τ) (↑rename ξ σ τ h) b)
renameSubst' ξ σ τ h ($ᵈ b a) = cong$ᵈ (renameSubst' ξ σ τ h b) (renameSubst' ξ σ τ h a)
renameSubst' ξ σ τ h mty = refl
renameSubst' ξ σ τ h (abs b) = cong abs (renameSubst' ξ σ τ h b)

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
subst∘' ρ σ τ h ∗ = refl
subst∘' ρ σ τ h (Π A j B) = congΠ (subst∘' ρ σ τ h A) refl (subst∘' (↑ ρ) (↑ σ) (↑ τ) (↑subst ρ σ τ h) B)
subst∘' ρ σ τ h (λᵈ b) = cong λᵈ (subst∘' (↑ ρ) (↑ σ) (↑ τ) (↑subst ρ σ τ h) b)
subst∘' ρ σ τ h ($ᵈ b a) = cong$ᵈ (subst∘' ρ σ τ h b) (subst∘' ρ σ τ h a)
subst∘' ρ σ τ h mty = refl
subst∘' ρ σ τ h (abs b) = cong abs (subst∘' ρ σ τ h b)

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

substUnion : ∀ σ a s → subst (a +: σ) s ≡ subst (a +: var) (subst (↑ σ) s)
substUnion σ a s = begin
  subst (a +: σ) s                                         ≡⟨ substExt _ _ (λ {zero → refl ; (suc n) → substDrop σ a n}) s ⟩
  subst (subst (a +: var) ∘ (var 0 +: (rename suc ∘ σ))) s ≡⟨ sym (subst∘ (a +: var) (↑ σ) s) ⟩
  (subst (a +: var) ∘ subst (var 0 +: (rename suc ∘ σ))) s ∎

substDist : ∀ σ a s → subst (subst σ a +: var) (subst (↑ σ) s) ≡ subst σ (subst (a +: var) s)
substDist σ a s = begin
  (subst (subst σ a +: var) ∘ subst (↑ σ)) s ≡⟨ sym (substUnion σ (subst σ a) s) ⟩
  subst (subst σ a +: σ) s                   ≡⟨ substExt _ _ (λ {zero → refl ; (suc n) → refl}) s ⟩
  subst (subst σ ∘ (a +: var)) s             ≡⟨ sym (subst∘ σ (a +: var) s) ⟩
  (subst σ ∘ subst (a +: var)) s ∎

{--------------------------
  Contexts and membership
--------------------------}
infix 30 _∷_#_
data Ctxt : Set where
  ∙ : Ctxt
  _∷_#_ : Ctxt → Term → Level → Ctxt

infix 40 _⦂_#_∈_
data _⦂_#_∈_ : Nat → Term → Level → Ctxt → Set where
  here  : ∀ {Γ A k} → 0 ⦂ (rename suc A) # k ∈ (Γ ∷ A # k)
  there : ∀ {Γ x A B k j} → x ⦂ A # k ∈ Γ → suc x ⦂ (rename suc A) # k ∈ (Γ ∷ B # j)