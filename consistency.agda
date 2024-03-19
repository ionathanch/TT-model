{-# OPTIONS --rewriting #-}

open import common
import accessibility
import syntactics
import reduction
import typing
import semantics
import soundness

module consistency where

{----------------------------------------------
  The naturals have a natural nonstrict order
----------------------------------------------}

data _≤_ : Nat → Nat → Set where
  zero : ∀ {n} → zero ≤ n
  suc : ∀ {n m} → n ≤ m → suc n ≤ suc m

refl≤ : ∀ {n} → n ≤ n
refl≤ {zero} = zero
refl≤ {suc n} = suc (refl≤ {n})

suc≤ : ∀ n → n ≤ suc n
suc≤ zero = zero
suc≤ (suc n) = suc (suc≤ n)

trans≤ : ∀ {n m k} → n ≤ m → m ≤ k → n ≤ k
trans≤ zero m≤k = zero
trans≤ (suc n≤m) (suc m≤k) = suc (trans≤ n≤m m≤k)

{--------------------------------------------------
  A maximum operator and its properties wrt order
--------------------------------------------------}

max : Nat → Nat → Nat
max zero zero = zero
max n zero = n
max zero m = m
max (suc n) (suc m) = suc (max n m)

maxₗ : ∀ n → max n zero ≡ n
maxₗ zero = refl
maxₗ (suc n) = refl

maxᵣ : ∀ m → max zero m ≡ m
maxᵣ zero = refl
maxᵣ (suc m) = refl

max≤ : ∀ n m → n ≤ max n m × m ≤ max n m
max≤ n zero rewrite maxₗ n = refl≤ , zero
max≤ zero m rewrite maxᵣ m = zero , refl≤
max≤ (suc n) (suc m) with p , q ← max≤ n m = suc p , suc q

{---------------------------------------------
  The nonstrict order induces a strict order
---------------------------------------------}

_<_ : Nat → Nat → Set
n < m = suc n ≤ m

suc< : ∀ n → n < suc n
suc< zero = suc (zero)
suc< (suc n) = suc (suc< n)

trans<' : ∀ {n m k} → n < m → m ≤ k → n < k
trans<' (suc n≤m) (suc m≤k) = suc (trans≤ n≤m m≤k)

trans< : ∀ {n m k} → n < m → m < k → n < k
trans< n<m m<k = trans<' n<m (trans≤ (suc≤ _) m<k)

max< : ∀ n m → n < suc (max n m) × m < suc (max n m)
max< n m with p , q ← max≤ n m = suc p , suc q

{-----------------------------------------------
  We instantiate our type theory's levels with
  the naturals and their transitive order;
  the naturals are well founded,
  so the type theory is consistent
-----------------------------------------------}

open accessibility Nat _<_

wfNat : ∀ k → Acc k
wfNat zero = acc< (λ ())
wfNat (suc k) with acc< f ← wfNat k = acc< (λ {(suc j≤k) → acc< (λ i<j → f (trans<' i<j j≤k))})

sup : ∀ i j → ∃[ k ] i < k × j < k × Acc k
sup i j with i< , j< ← max< i j = suc (max i j) , i< , j< , wfNat (suc (max i j))

succ : ∀ j → ∃[ k ] j < k × Acc k
succ j = suc j , suc< j , wfNat (suc j)

open syntactics Nat
open reduction Nat
open typing Nat _<_ trans<
open semantics Nat _<_ trans< sup
open soundness Nat _<_ trans< sup succ

consistency : ∀ {b} → ∙ ⊢ b ⦂ mty → ⊥
consistency tb
  with k , acck , b , elb ← soundness {σ = var} ∙̂  tt tb
  with () ← empty acck b elb