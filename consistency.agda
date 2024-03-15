open import common
import accessibility
import syntactics
import reduction
import typing
import semantics
import soundness

module consistency where

{-----------------------------------------
  The naturals have a nonstrict order,
  which naturally induces a strict order
-----------------------------------------}

data _≤_ : Nat → Nat → Set where
  zero : ∀ {n} → zero ≤ n
  suc : ∀ {n m} → n ≤ m → suc n ≤ suc m

suc≤ : ∀ n → n ≤ suc n
suc≤ zero = zero
suc≤ (suc n) = suc (suc≤ n)

trans≤ : ∀ {n m k} → n ≤ m → m ≤ k → n ≤ k
trans≤ zero m≤k = zero
trans≤ (suc n≤m) (suc m≤k) = suc (trans≤ n≤m m≤k)

_<_ : Nat → Nat → Set
n < m = suc n ≤ m

trans<' : ∀ {n m k} → n < m → m ≤ k → n < k
trans<' (suc n≤m) (suc m≤k) = suc (trans≤ n≤m m≤k)

trans< : ∀ {n m k} → n < m → m < k → n < k
trans< n<m m<k = trans<' n<m (trans≤ (suc≤ _) m<k)

{-----------------------------------------------
  We instantiate our type theory's levels with
  the naturals and their transitive order;
  the naturals are well founded,
  so the type theory is consistent
-----------------------------------------------}

open accessibility Nat _<_
open syntactics Nat
open reduction Nat
open typing Nat _<_ trans<
open semantics Nat _<_ trans<
open soundness Nat _<_ trans<

wfNat : ∀ k → Acc k
wfNat zero = acc< (λ ())
wfNat (suc k) with acc< f ← wfNat k = acc< (λ {(suc j≤k) → acc< (λ i<j → f (trans<' i<j j≤k))})

consistency : ∀ {k b} → ∙ ⊢ b ⦂ mty # k → ⊥
consistency {k} tb
  with b , elb ← soundness {σ = var} (wfNat k) ∙̂  tt tb
  with () ← empty (wfNat k) b elb