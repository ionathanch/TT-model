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
  êq : ∀ c → (C : U' k U< c) →
       ∀ a → el' k U< a C →
       ∀ b → el' k U< b C →
       U' k U< (eq c a b)
  𝔹̂ : U' k U< 𝔹
  ⇒̂  : ∀ a b → a ⇒ b → U' k U< b → U' k U< a

el' k U< T (Û j j<k) = U< j<k T
el' k U< _ ⊥̂  = ⊥
el' k U< f (Π̂ _ A _ B) = ∀ x → (a : el' k U< x A) → el' k U< ($ᵈ f x) (B x a)
el' k U< p (êq _ _ a _ b _) = p ⇒⋆ refl × a ⇔ b
el' k U< b 𝔹̂ = b ⇒⋆ true ⊎ b ⇒⋆ false
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

{----------------------------------
  Cumulativity given j<k:
  * ⟦A⟧ⱼ can be lifted to ⟦A⟧ₖ
  * a ∈ ⟦A⟧ⱼ is equal to a ∈ ⟦A⟧ₖ
----------------------------------}

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
cumU accj acck j<k (êq c C a A b B) =
  let qa = cumEl accj acck j<k C
      qb = cumEl accj acck j<k C
  in êq c (cumU accj acck j<k C) a (coe qa A) b (coe qb B)
cumU _ _ _ 𝔹̂ = 𝔹̂
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
cumEl accj@(acc< _) acck@(acc< _) j<k (êq _ _ _ _ _ _) = refl
cumEl (acc< _) (acc< _) _ 𝔹̂ = refl
cumEl accj@(acc< _) acck@(acc< _) j<k (⇒̂  a b a⇒b B) = cumEl accj acck j<k B

{-------------------------------------------------------
  Propositional irrelevance of interpretations:
  two proofs of a ∈ 〚A⟧ₖ are propositionally equal,
  even given different sets 〚A⟧ₖ at different levels,
  for convertible A
-------------------------------------------------------}

-- First, irrelevance across U of the same level
el≡' : ∀ {k a A₁ A₂} (acc : Acc k)
       (u₁ : U k acc A₁) (u₂ : U k acc A₂) →
       A₁ ⇔ A₂ → el k acc a u₁ ↔ el k acc a u₂
el≡' (acc< f) (Û _ j<k₁) (Û _ j<k₂) 𝒰₁⇔𝒰₂
  with refl ← ⇔-𝒰-inv 𝒰₁⇔𝒰₂ = accU (f j<k₁) (f j<k₂) , accU (f j<k₂) (f j<k₁)
el≡' acc ⊥̂ ⊥̂ _ = id , id
el≡' acc (Π̂ a₁ A₁ b₁ B₁) (Π̂ a₂ A₂ b₂ B₂) Πab₁⇔Πab₂ =
  let a₁⇔a₂ , b₁⇔b₂ = ⇔-Π-inv Πab₁⇔Πab₂ in
  (λ elB x elA →
    let fA , gA = el≡' acc A₁ A₂ a₁⇔a₂
        fB , gB = el≡' acc (B₁ x (gA elA)) (B₂ x elA) (⇔-cong ⇔-refl b₁⇔b₂)
    in fB (elB x (gA elA))) ,
  (λ elB x elA →
    let fA , gA = el≡' acc A₁ A₂ a₁⇔a₂
        fB , gB = el≡' acc (B₁ x elA) (B₂ x (fA elA)) (⇔-cong ⇔-refl b₁⇔b₂)
    in gB (elB x (fA elA)))
el≡' acc (êq c₁ C₁ a₁ A₁ b₁ B₁) (êq c₂ C₂ a₂ A₂ b₂ B₂) eq⇔eq =
  let _ , a₁⇔a₂ , b₁⇔b₂ = ⇔-eq-inv eq⇔eq in
  (λ {(p⇒⋆refl , a₁⇔b₁) → p⇒⋆refl , ⇔-trans (⇔-sym a₁⇔a₂) (⇔-trans a₁⇔b₁ b₁⇔b₂)}) ,
  (λ {(p⇒⋆refl , a₂⇔b₂) → p⇒⋆refl , ⇔-trans (⇔-trans a₁⇔a₂ a₂⇔b₂) (⇔-sym b₁⇔b₂)})
el≡' acc 𝔹̂ 𝔹̂ _ = id , id
el≡' acc (⇒̂  a₁ a₂ a₁⇒a₂ u₁) u₂ a₁⇔a₃ =
  el≡' acc u₁ u₂ (⇔-trans (⇔-sym (⇒-⇔ a₁⇒a₂)) a₁⇔a₃)
el≡' acc u₁ (⇒̂  a₂ a₃ a₂⇒a₃ u₂) a₁⇔a₂ =
  el≡' acc u₁ u₂ (⇔-trans a₁⇔a₂ (⇒-⇔ a₂⇒a₃))
el≡' _ (Û _ _) ⊥̂ 𝒰⇔mty with () ← ⇎-𝒰mty 𝒰⇔mty
el≡' _ (Û _ _) (Π̂ _ _ _ _) 𝒰⇔Π with () ← ⇎-𝒰Π 𝒰⇔Π
el≡' _ ⊥̂ (Π̂ _ _ _ _) mty⇔Π with () ← ⇎-mtyΠ mty⇔Π
el≡' _ ⊥̂ (Û _ _) mty⇔𝒰 with () ← ⇎-𝒰mty (⇔-sym mty⇔𝒰)
el≡' _ (Π̂ _ _ _ _) (Û _ _) Π⇔𝒰 with () ← ⇎-𝒰Π (⇔-sym Π⇔𝒰)
el≡' _ (Π̂ _ _ _ _) ⊥̂ Π⇔mty with () ← ⇎-mtyΠ (⇔-sym Π⇔mty)
el≡' _ (Û _ _) (êq _ _ _ _ _ _) 𝒰⇔eq with () ← ⇎-𝒰eq 𝒰⇔eq
el≡' _ (êq _ _ _ _ _ _) (Û _ _) eq⇔𝒰 with () ← ⇎-𝒰eq (⇔-sym eq⇔𝒰)
el≡' _ ⊥̂ (êq _ _ _ _ _ _) mty⇔eq with () ← ⇎-mtyeq mty⇔eq
el≡' _ (êq _ _ _ _ _ _) ⊥̂ eq⇔mty with () ← ⇎-mtyeq (⇔-sym eq⇔mty)
el≡' _ (Π̂ _ _ _ _) (êq _ _ _ _ _ _) Π⇔eq with () ← ⇎-Πeq Π⇔eq
el≡' _ (êq _ _ _ _ _ _) (Π̂ _ _ _ _) eq⇔Π with () ← ⇎-Πeq (⇔-sym eq⇔Π)
el≡' _ (Û _ _) 𝔹̂ 𝒰⇔𝔹 with () ← ⇎-𝒰𝔹 𝒰⇔𝔹
el≡' _ 𝔹̂ (Û _ _) 𝔹⇔𝒰 with () ← ⇎-𝒰𝔹 (⇔-sym 𝔹⇔𝒰)
el≡' _ ⊥̂ 𝔹̂ 𝔹⇔eq with () ← ⇎-mty𝔹 𝔹⇔eq
el≡' _ 𝔹̂ ⊥̂ eq⇔𝔹 with () ← ⇎-mty𝔹 (⇔-sym eq⇔𝔹)
el≡' _ (Π̂ _ _ _ _) 𝔹̂ Π⇔𝔹 with () ← ⇎-Π𝔹 Π⇔𝔹
el≡' _ 𝔹̂ (Π̂ _ _ _ _) 𝔹⇔Π with () ← ⇎-Π𝔹 (⇔-sym 𝔹⇔Π)
el≡' _ (êq _ _ _ _ _ _) 𝔹̂ eq⇔𝔹 with () ← ⇎-eq𝔹 eq⇔𝔹
el≡' _ 𝔹̂ (êq _ _ _ _ _ _) 𝔹⇔eq with () ← ⇎-eq𝔹 (⇔-sym 𝔹⇔eq)

-- Cumulativity and the existence of suprema
-- gives us irrelevance across different levels
el≡ : ∀ {k₁ k₂} (acck₁ : Acc k₁) (acck₂ : Acc k₂) {t T₁ T₂ : Term}
         (u₁ : U k₁ acck₁ T₁) (u₂ : U k₂ acck₂ T₂) →
         T₁ ⇔ T₂ → el k₁ acck₁ t u₁ → el k₂ acck₂ t u₂
el≡ {k₁} {k₂} acck₁ acck₂ u₁ u₂ T₁⇔T₂ elt =
  let ℓ , k₁<ℓ , k₂<ℓ , accℓ = sup k₁ k₂
      f , _ = el≡' accℓ (cumU acck₁ accℓ k₁<ℓ u₁) (cumU acck₂ accℓ k₂<ℓ u₂) T₁⇔T₂
      p = cumEl acck₁ accℓ k₁<ℓ u₁
      q = cumEl acck₂ accℓ k₂<ℓ u₂
  in coe (sym q) (f (coe p elt))

-- el≡ specialized to identical syntactic types
el→ : ∀ {k₁ k₂} (acck₁ : Acc k₁) (acck₂ : Acc k₂) {t T : Term}
      (u₁ : U k₁ acck₁ T) (u₂ : U k₂ acck₂ T) →
      el k₁ acck₁ t u₁ → el k₂ acck₂ t u₂
el→ acck₁ acck₂ u₁ u₂ = el≡ acck₁ acck₂ u₁ u₂ ⇔-refl

-- el≡ specialized to identical proofs of accessibility
⇔-el : ∀ {k a A B} (acc : Acc k)
       (uA : U k acc A) (uB : U k acc B) (A⇔B : A ⇔ B) →
       el k acc a uA → el k acc a uB
⇔-el {k} acc uA uB A⇔B = el≡ acc acc uA uB A⇔B

-- Could use ⇔-el since A ≡ B → A ⇔ B by ⇔-refl, but that's a little silly
≡-el : ∀ {k t A A'} acc (u : U k acc A) (p : A ≡ A') →
       el k acc t u → el k acc t (transp (U k acc) p u)
≡-el acc u refl elA = elA

{--------------------------------------
  Backward preservation given a ⇒⋆ b:
  * if ⟦b⟧ₖ then ⟦a⟧ₖ
  * if b ∈ ⟦A⟧ₖ then a ∈ ⟦A⟧ₖ
--------------------------------------}

⇒⋆-U : ∀ {k} (acc : Acc k) {a b} → a ⇒⋆ b → U k acc b → U k acc a
⇒⋆-U _ (⇒⋆-refl a) u = u
⇒⋆-U acc (⇒⋆-trans a⇒b b⇒⋆c) u = ⇒̂ _ _ a⇒b (⇒⋆-U acc b⇒⋆c u)

⇒-el : ∀ {k} (acc : Acc k) {a b A} (u : U k acc A) → a ⇒ b → el k acc b u → el k acc a u
⇒-el (acc< f) (Û j j<k) a⇒b = ⇒⋆-U (f j<k) (⇒-⇒⋆ a⇒b)
⇒-el acc (Π̂ _ A _ B) a⇒b elB x elA = ⇒-el acc (B x elA) (⇒-$ᵈ a⇒b (⇒-refl x)) (elB x elA)
⇒-el acc {p} {q} (êq _ C a A b B) p⇒q (q⇒⋆refl , abc) = ⇒⋆-trans p⇒q q⇒⋆refl , abc
⇒-el acc 𝔹̂ a⇒b (inj₁ b⇒⋆true) = inj₁ (⇒⋆-trans a⇒b b⇒⋆true)
⇒-el acc 𝔹̂ a⇒b (inj₂ b⇒⋆false) = inj₂ (⇒⋆-trans a⇒b b⇒⋆false)
⇒-el acc (⇒̂  A B A⇒B u) a⇒b = ⇒-el acc u a⇒b

⇒⋆-el : ∀ {k} (acc : Acc k) {a b A} (u : U k acc A) → a ⇒⋆ b → el k acc b u → el k acc a u
⇒⋆-el acc u (⇒⋆-refl a) elU = elU
⇒⋆-el acc u (⇒⋆-trans a⇒b b⇒⋆c) elU = ⇒-el acc u a⇒b (⇒⋆-el acc u b⇒⋆c elU)

{----------------------------------
  Subject reduction given a ⇒⋆ b:
  * if ⟦a⟧ₖ then ⟦b⟧ₖ, and
  * if a ∈ ⟦A⟧ₖ then b ∈ ⟦A⟧ₖ
----------------------------------}

SRU  : ∀ {k} (acc : Acc k) {a b} → a ⇒ b → U k acc a → U k acc b
SRel : ∀ {k} (acc : Acc k) {A a b} → a ⇒ b → (u : U k acc A) → el k acc a u → el k acc b u

SRU acc {b = b} a⇒b (⇒̂  a c a⇒c C) =
  let d , b⇒d , c⇒d = diamond a⇒b a⇒c
  in ⇒̂  b d b⇒d (SRU acc c⇒d C)
SRU acc (⇒-𝒰 _) (Û _ j<k) = Û _ j<k
SRU acc ⇒-mty ⊥̂ = ⊥̂
SRU acc (⇒-Π a⇒a' b⇒b') (Π̂ _ A _ B) =
  Π̂ _ (SRU acc a⇒a' A)
    _ (λ x elA → SRU acc (⇒-cong (⇒-refl x) b⇒b')
        (B x (⇔-el acc (SRU acc a⇒a' A) A (⇔-sym (⇒-⇔ a⇒a')) elA)))
SRU acc (⇒-eq {a' = a'} {b' = b'} A⇒A' a⇒a' b⇒b') (êq _ C _ elA _ elB) =
  let elA' = ⇔-el acc C (SRU acc A⇒A' C) (⇒-⇔ A⇒A') (SRel acc a⇒a' C elA)
      elB' = ⇔-el acc C (SRU acc A⇒A' C) (⇒-⇔ A⇒A') (SRel acc b⇒b' C elB)
  in êq _ (SRU acc A⇒A' C) a' elA' b' elB'
SRU acc ⇒-𝔹 𝔹̂ = 𝔹̂

SRel acc a⇒b (⇒̂  _ _ _ C) = SRel acc a⇒b C
SRel (acc< f) a⇒b (Û _ j<k) = SRU (f j<k) a⇒b
SRel acc _ ⊥̂ = id
SRel acc a⇒b (Π̂ a A b B) f x elA = SRel acc (⇒-$ᵈ a⇒b (⇒-refl x)) (B x elA) (f x elA)
SRel acc p⇒q (êq c C a A b B) (p⇒⋆refl , a⇔b) =
  let _ , refl⇒⋆r , q⇒⋆r = diacon p⇒⋆refl p⇒q
      r≡refl = ⇒⋆-refl-inv refl⇒⋆r
  in transp (_ ⇒⋆_) r≡refl q⇒⋆r , a⇔b
SRel acc a⇒b 𝔹̂ (inj₁ a⇒⋆true) =
  let _ , true⇒⋆c , b⇒⋆c = diacon a⇒⋆true a⇒b
      c≡true = ⇒⋆-true-inv true⇒⋆c
  in inj₁ (transp (_ ⇒⋆_) c≡true b⇒⋆c)
SRel acc a⇒b 𝔹̂ (inj₂ a⇒⋆false) =
  let _ , false⇒⋆c , b⇒⋆c = diacon a⇒⋆false a⇒b
      c≡false = ⇒⋆-false-inv false⇒⋆c
  in inj₂ (transp (_ ⇒⋆_) c≡false b⇒⋆c)

SRU⋆ : ∀ {k a b} acc → a ⇒⋆ b → U k acc a → U k acc b
SRU⋆ acc (⇒⋆-refl a) u = SRU acc (⇒-refl a) u
SRU⋆ acc (⇒⋆-trans a⇒b b⇒⋆c) u = SRU⋆ acc b⇒⋆c (SRU acc a⇒b u)

-- Why do we never need a ⇒⋆ b → el k acc a → el k acc b?

{----------------------------------------------------------
  Corollary of backward preservation + subject reduction:
  given a ⇔ b, if ⟦a⟧ₖ then ⟦b⟧ₖ
----------------------------------------------------------}

⇔-U : ∀ {k a b} acc → a ⇔ b → U k acc a → U k acc b
⇔-U acc (_ , a⇒⋆c , b⇒⋆c) u = ⇒⋆-U acc b⇒⋆c (SRU⋆ acc a⇒⋆c u)

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

-- Inversion on semantic equality type
inveq-U : ∀ {c a b k} (acc : Acc k) → U k acc (eq c a b) →
          Σ[ C ∈ U k acc c ] el k acc a C × el k acc b C
inveq-U acc (êq _ C _ ela _ elb) = C , ela , elb
inveq-U acc (⇒̂  (eq c a b) (eq c' a' b') (⇒-eq c⇒c' a⇒a' b⇒b') u) =
  let C' , ela' , elb' = inveq-U acc u
  in ⇒̂  c c' c⇒c' C' , ⇒-el acc C' a⇒a' ela' , ⇒-el acc C' b⇒b' elb'

-- Inversion on semantic equalities
inveq-el : ∀ {c a b k} (acc : Acc k) (u : U k acc (eq c a b)) p →
           el k acc p u → p ⇒⋆ refl × a ⇔ b
inveq-el acc (êq _ _ _ _ _ _) _ = id
inveq-el acc (⇒̂  (eq c a b) (eq c' a' b') (⇒-eq c⇒c' a⇒a' b⇒b') u) p elp =
  let p⇒⋆refl , a'⇔b' = inveq-el acc u p elp
  in p⇒⋆refl , ⇔-trans (⇔-trans (⇒-⇔ a⇒a') a'⇔b') (⇔-sym (⇒-⇔ b⇒b'))

-- Inversion on semantic booleans
inv𝔹-el : ∀ {b : Term} {k : Level} (acc : Acc k) (u : U k acc 𝔹) →
          el k acc b u → b ⇒⋆ true ⊎ b ⇒⋆ false
inv𝔹-el acc 𝔹̂ = id
inv𝔹-el acc (⇒̂ 𝔹 𝔹 ⇒-𝔹 u) elb = inv𝔹-el acc u elb

{--------------------------------------
  Semantic well-formedness:
  σ ∈ ⟦Γ⟧ = x ⦂ A ∈ Γ → σ x ∈ ⟦A{σ}⟧ₖ
--------------------------------------}

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