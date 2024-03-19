{-# OPTIONS --rewriting #-}

open import common
import accessibility
import syntactics
import reduction

module semantics
  (Level : Set)
  (_<_ : Level → Level → Set)
  (trans< : ∀ {i j k} → i < j → j < k → i < k)
  (open accessibility Level _<_)
  (sup : ∀ i j → ∃[ k ] i < k × j < k × Acc k) where
open syntactics Level
open reduction Level

data U' k (U< : ∀ {j} → j < k → Term → Set) : Term → Set
el' : ∀ k (U< : ∀ {j} → j < k → Term → Set) → Term → ∀ {T} → U' k U< T → Set

data U' k U< where
  Û : ∀ j → j < k → U' k U< (𝒰 j)
  ⊥̂ : U' k U< mty
  Π̂ : ∀ a → (A : U' k U< a) →
      ∀ b → (∀ x → el' k U< x A → U' k U< (subst (x +: var) b)) →
      U' k U< (Π a b)
  ⇒̂  : ∀ a b → a ⇒ b → U' k U< b → U' k U< a

el' k U< T (Û j j<k) = U< j<k T
el' k U< _ ⊥̂  = ⊥
el' k U< f (Π̂ _ A _ B) = ∀ x → (a : el' k U< x A) → el' k U< ($ᵈ f x) (B x a)
el' k U< x (⇒̂  a b a⇒b A) = el' k U< x A

-- U' k and el' k are parametrized by U< j, where j < k;
-- we instantiate the parameters by induction on accessibility of levels

U<  : ∀ {k} → Acc k → ∀ {j} → j < k → Term → Set
el< : ∀ {k} (p : Acc k) {j} (j<k : j < k) → Term → ∀ {T} → U< p j<k T → Set

U<  (acc< f) {j} j<k T = U'  j (U< (f j<k)) T
el< (acc< f) {j} j<k t = el' j (U< (f j<k)) t

-- We tie the knot by instantiating U< and el<

U : ∀ k (acc : Acc k) → Term → Set
U k acc T = U' k (U< acc) T

el : ∀ k (acc : Acc k) → Term → ∀ {T} → U k acc T → Set
el k acc t = el' k (U< acc) t

{----------------------------------------
  Irrelevance of accessibility across U
----------------------------------------}

accU≡ : ∀ {k T} (acc₁ acc₂ : Acc k) → U k acc₁ T ≡ U k acc₂ T
accU≡ acc₁ acc₂ with refl ← (let open ext in accProp acc₁ acc₂) = refl

accU : ∀ {k T} (acc₁ acc₂ : Acc k) → U k acc₁ T → U k acc₂ T
accU acc₁ acc₂ = coe (accU≡ acc₁ acc₂)

accU< : ∀ {j k T} (accj : Acc j) (acck : Acc k) (j<k : j < k) → U j accj T → U< acck j<k T
accU< accj (acc< f) j<k = accU accj (f j<k)

{------------------------------------------
  Cumulativity:
  * Given j < k, U j can be lifted to U k
  * Given j < k and u : U j,
    the interpretation of u and
    the interpretation of the lifted u
    are equal
------------------------------------------}

cumU : ∀ {j k} (accj : Acc j) (acck : Acc k) → j < k → {T : Term} →
       U j accj T → U k acck T

cumEl : ∀ {j k} (accj : Acc j) (acck : Acc k) (j<k : j < k) {t T : Term} (u : U j accj T) →
        el j accj t u ≡ el k acck t (cumU accj acck j<k u)

cumU (acc< f) (acc< g) j<k (Û i i<j) = Û i (trans< i<j j<k)
cumU _ _ _ ⊥̂  = ⊥̂
cumU accj acck j<k (Π̂ a A b B) =
  Π̂ a (cumU accj acck j<k A)
    b (λ x a →
         let p = cumEl accj acck j<k A
         in cumU accj acck j<k (B x (coe (sym p) a)))
cumU accj acck j<k (⇒̂  a b a⇒b B) = ⇒̂  a b a⇒b (cumU accj acck j<k B)

cumEl (acc< f) (acc< g) j<k (Û i i<j) = accU≡ (f i<j) (g (trans< i<j j<k))
cumEl (acc< _) (acc< _) _ ⊥̂  = refl
cumEl accj@(acc< _) acck@(acc< _) j<k {t = t} (Π̂ a A b B) =
  let open ext in
  piext refl (λ x →
    let p = cumEl accj acck j<k A in
    piext p (λ a →
      let B' = λ a → cumU accj acck j<k (B x a)
          q = cumEl accj acck j<k (B x a)
      in trans q (cong (λ a → el' _ _ _ (B' a)) (sym (coe-β p a)))))
cumEl accj@(acc< _) acck@(acc< _) j<k (⇒̂  a b a⇒b B) = cumEl accj acck j<k B

{-------------------------------------------------------
  Propositional irrelevance of interpretations:
  two proofs of a ∈ 〚A⟧ₖ are propositionally equal,
  even given different sets 〚A⟧ₖ at different levels,
  for convertible A
-------------------------------------------------------}

-- First, irrelevance across U of the same level
el≡' : ∀ {k a A₁ A₂} (acc₁ acc₂ : Acc k)
       (u₁ : U k acc₁ A₁) (u₂ : U k acc₂ A₂) →
       A₁ ⇔ A₂ → el k acc₁ a u₁ ≡ el k acc₂ a u₂
el≡' (acc< f) (acc< g) (Û _ j<k₁) (Û _ j<k₂) 𝒰₁⇔𝒰₂
  with refl ← ⇔-𝒰-inv 𝒰₁⇔𝒰₂ = accU≡ (f j<k₁) (g j<k₂)
el≡' acc₁ acc₂ ⊥̂ ⊥̂ _ = refl
el≡' acc₁ acc₂ (Π̂ a₁ A₁ b₁ B₁) (Π̂ a₂ A₂ b₂ B₂) Πab₁⇔Πab₂ =
  let a₁⇔a₂ , b₁⇔b₂ = ⇔-Π-inv Πab₁⇔Πab₂
      open ext in
  piext refl (λ x →
    let ela≡ = el≡' acc₁ acc₂ A₁ A₂ a₁⇔a₂ in
    piext ela≡ (λ a →
      el≡' acc₁ acc₂ (B₁ x a) (B₂ x (coe ela≡ a)) (⇔-cong ⇔-refl b₁⇔b₂)))
el≡' acc₁ acc₂ (⇒̂  a₁ a₂ a₁⇒a₂ u₁) u₂ a₁⇔a₃ =
  el≡' acc₁ acc₂ u₁ u₂ (⇔-trans (⇔-sym (⇒-⇔ a₁⇒a₂)) a₁⇔a₃)
el≡' acc₁ acc₂ u₁ (⇒̂  a₂ a₃ a₂⇒a₃ u₂) a₁⇔a₂ =
  el≡' acc₁ acc₂ u₁ u₂ (⇔-trans a₁⇔a₂ (⇒-⇔ a₂⇒a₃))
el≡' _ _ (Û _ _) ⊥̂ 𝒰⇔mty with () ← ⇎⋆-𝒰mty 𝒰⇔mty
el≡' _ _ (Û _ _) (Π̂ _ _ _ _) 𝒰⇔Π with () ← ⇎⋆-𝒰Π 𝒰⇔Π
el≡' _ _ ⊥̂ (Π̂ _ _ _ _) mty⇔Π with () ← ⇎⋆-mtyΠ mty⇔Π
el≡' _ _ ⊥̂ (Û _ _) mty⇔𝒰 with () ← ⇎⋆-𝒰mty (⇔-sym mty⇔𝒰)
el≡' _ _ (Π̂ _ _ _ _) (Û _ _) Π⇔𝒰 with () ← ⇎⋆-𝒰Π (⇔-sym Π⇔𝒰)
el≡' _ _ (Π̂ _ _ _ _) ⊥̂ Π⇔mty with () ← ⇎⋆-mtyΠ (⇔-sym Π⇔mty)

-- Cumulativity and the existence of suprema
-- gives us irrelevance across different levels
el≡ : ∀ {k₁ k₂} (acck₁ : Acc k₁) (acck₂ : Acc k₂) {t T₁ T₂ : Term}
         (u₁ : U k₁ acck₁ T₁) (u₂ : U k₂ acck₂ T₂) →
         T₁ ⇔ T₂ → el k₁ acck₁ t u₁ ≡ el k₂ acck₂ t u₂
el≡ {k₁} {k₂} acck₁ acck₂ u₁ u₂ T₁⇔T₂ =
  let ℓ , k₁<ℓ , k₂<ℓ , accℓ = sup k₁ k₂
  in begin
    el k₁ acck₁ _ u₁                        ≡⟨ cumEl acck₁ accℓ k₁<ℓ u₁ ⟩
    el ℓ  accℓ  _ (cumU acck₁ accℓ k₁<ℓ u₁) ≡⟨ el≡' accℓ accℓ
                                                      (cumU acck₁ accℓ k₁<ℓ u₁)
                                                      (cumU acck₂ accℓ k₂<ℓ u₂) T₁⇔T₂ ⟩
    el ℓ  accℓ  _ (cumU acck₂ accℓ k₂<ℓ u₂) ≡⟨ sym (cumEl acck₂ accℓ k₂<ℓ u₂) ⟩
    el k₂ acck₂ _ u₂ ∎

-- el≡ specialized to identical syntactic types
el→ : ∀ {k₁ k₂} (acck₁ : Acc k₁) (acck₂ : Acc k₂) {t T : Term}
      (u₁ : U k₁ acck₁ T) (u₂ : U k₂ acck₂ T) →
      el k₁ acck₁ t u₁ → el k₂ acck₂ t u₂
el→ acck₁ acck₂ u₁ u₂ = coe (el≡ acck₁ acck₂ u₁ u₂ ⇔-refl)

-- el≡ specialized to identical proofs of accessibility
⇔-el : ∀ {k a A B} (acc : Acc k)
       (uA : U k acc A) (uB : U k acc B) (A⇔B : A ⇔ B) →
       el k acc a uA → el k acc a uB
⇔-el {k} acc uA uB A⇔B = coe (el≡ acc acc uA uB A⇔B)

-- Could use ⇔-el since A ≡ B → A ⇔ B by ⇔-refl, but that's a little silly
≡-el : ∀ {k t A A'} acc (u : U k acc A) (p : A ≡ A') →
       el k acc t u → el k acc t (transp (U k acc) p u)
≡-el acc u refl elA = elA

{-------------------
  Inversion lemmas
--------------------}

-- Universes are à la Russell
el-U : ∀ {j k A} (acc : Acc k) (u : U k acc (𝒰 j)) → el k acc A u → Σ[ acc' ∈ Acc j ] j < k × U j acc' A
el-U (acc< f) (Û j j<k) elU = f j<k , j<k , elU
el-U acc (⇒̂  (𝒰 j) (𝒰 j) (⇒-𝒰 j) u) elU = el-U acc u elU

-- Nothing lives in the empty type
empty : ∀ {k t} acc (u : U k acc mty) → el k acc t u → ⊥
empty acc ⊥̂  ()
empty acc (⇒̂  mty mty ⇒⋆-mty u) = empty acc u

-- Inversion on semantic function type
invΠ-U : ∀ {a b k} (acc : Acc k) → U k acc (Π a b) →
         Σ[ A ∈ U k acc a ] ∀ x → el k acc x A → U k acc (subst (x +: var) b)
invΠ-U acc (Π̂ a A b B) = A , B
invΠ-U acc (⇒̂  (Π a b) (Π a' b') (⇒-Π a⇒a' b⇒b') u) =
  let A' , B' = invΠ-U acc u
  in ⇒̂  a a' a⇒a' A' , λ x elA → ⇒̂  _ _ (⇒-cong (⇒-refl x) b⇒b') (B' x elA)

-- Inversion on semantic functions
invΠ-el : ∀ {a b k} (acc : Acc k) (u : U k acc (Π a b)) f → el k acc f u →
          let A , B = invΠ-U acc u in
          ∀ x → (a : el k acc x A) → el k acc ($ᵈ f x) (B x a)
invΠ-el acc (Π̂ a A b B) f elB x elA = elB x elA
invΠ-el acc (⇒̂  (Π a b) (Π a' b') (⇒-Π a⇒a' b⇒b') u) = invΠ-el acc u

{----------------------------------------------------
  Backward preservation of U, el with respect to ⇒⋆
----------------------------------------------------}

⇒⋆-U : ∀ {k} (acc : Acc k) {a b} → a ⇒⋆ b → U k acc b → U k acc a
⇒⋆-U _ (⇒⋆-refl a) u = u
⇒⋆-U acc (⇒⋆-trans a⇒b b⇒⋆c) u = ⇒̂ _ _ a⇒b (⇒⋆-U acc b⇒⋆c u)

⇒-el : ∀ {k} (acc : Acc k) {a b A} (u : U k acc A) → a ⇒ b → el k acc b u → el k acc a u
⇒-el (acc< f) (Û j j<k) a⇒b = ⇒⋆-U (f j<k) (⇒-⇒⋆ a⇒b)
⇒-el acc (Π̂ _ A _ B) a⇒b elB x elA = ⇒-el acc (B x elA) (⇒-$ᵈ a⇒b (⇒-refl x)) (elB x elA)
⇒-el acc (⇒̂  A B A⇒B u) a⇒b = ⇒-el acc u a⇒b

⇒⋆-el : ∀ {k} (acc : Acc k) {a b A} (u : U k acc A) → a ⇒⋆ b → el k acc b u → el k acc a u
⇒⋆-el acc u (⇒⋆-refl a) elU = elU
⇒⋆-el acc u (⇒⋆-trans a⇒b b⇒⋆c) elU = ⇒-el acc u a⇒b (⇒⋆-el acc u b⇒⋆c elU)

{---------------------------------
  Subject reduction of U:
  if a ⇒⋆ b and U k a then U k b
---------------------------------}

SRU  : ∀ {k} (acc : Acc k) {a b} → a ⇒ b → U k acc a → U k acc b
SRU acc (⇒-𝒰 _) (Û _ j<k) = Û _ j<k
SRU acc ⇒-mty ⊥̂ = ⊥̂
SRU acc (⇒-Π {a' = a'} {b' = b'} a⇒a' b⇒b') (Π̂ a A b B) =
  Π̂ a' (SRU acc a⇒a' A)
    b' (λ x elA → SRU acc (⇒-cong (⇒-refl x) b⇒b')
          (B x (⇔-el acc (SRU acc a⇒a' A) A (⇔-sym (⇒-⇔ a⇒a')) elA)))
SRU acc {b = b} a⇒b (⇒̂  a c a⇒c C) =
  let d , b⇒d , c⇒d = diamond a⇒b a⇒c
  in ⇒̂  b d b⇒d (SRU acc c⇒d C)

SRU⋆ : ∀ {k a b} acc → a ⇒⋆ b → U k acc a → U k acc b
SRU⋆ acc (⇒⋆-refl a) u = SRU acc (⇒-refl a) u
SRU⋆ acc (⇒⋆-trans a⇒b b⇒⋆c) u = SRU⋆ acc b⇒⋆c (SRU acc a⇒b u)

⇔-U : ∀ {k a b} acc → a ⇔ b → U k acc a → U k acc b
⇔-U acc (_ , a⇒⋆c , b⇒⋆c) u = ⇒⋆-U acc b⇒⋆c (SRU⋆ acc a⇒⋆c u)

{-----------------------------------------
  Semantic well-formedness:
    σ ∈ ⟦Γ⟧ = x ⦂ A # k ∈ Γ → σ x ∈ ⟦A⟧ₖ
-----------------------------------------}

data V : Ctxt → Set
em : ∀ (σ : Nat → Term) {Γ} → V Γ → Set

data V where
  ∙̂  : V ∙
  ∷̂  : ∀ {Γ A} (v : V Γ) → (∀ σ → em σ v → ∃[ k ] Σ[ acc ∈ Acc k ] U k acc (subst σ A)) → V (Γ ∷ A)

em σ ∙̂  = ⊤
em σ (∷̂  v w) =
  Σ[ emV ∈ em (σ ∘ suc) v ]
    let k , acc , u = w (σ ∘ suc) emV
    in el k acc (σ 0) u