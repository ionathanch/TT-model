# Mechanization of consistency, Lean edition

This is a Lean mechanization of a type theory with first-class universe levels,
also based on @yiyunliu's [mltt-consistency](https://github.com/yiyunliu/mltt-consistency)
proof written in Rocq.
This mechanization is closer in style than the one in Agda,
since the logical relation takes advantage of Lean's impredicative Prop
in place of induction–recursion.
It has been checked with Lean 4.13.0-rc3 and requires Mathlib for some typeclasses.
The development can be checked and built using `lake build`.

## Type Theory

The object theory is a type theory with universes à la Russell,
first-class bounded levels, simple cumulativity, dependent functions, an empty type,
and untyped conversion.
First, the below is an overview of the last three features,
which should appear unsurprising compared to what was mechanized in Agda.
Again, the overview uses variable names, while the mechanization uses de Bruijn indexing.

```
                Γ ⊢ B : 𝒰 k
x : A ∈ Γ    Γ ⊢ a : A    A ≈ B
---------    ------------------
Γ ⊢ x : A        Γ ⊢ a : B

    Γ ⊢ A : 𝒰 k            Γ ⊢ Πx : A. B           Γ ⊢ b : Πx: A. B
Γ, x : A ⊢ B : 𝒰 k        Γ, x : A ⊢ b : B            Γ ⊢ a : A
--------------------    ----------------------    -------------------
Γ ⊢ Πx : A. B : 𝒰 k     Γ ⊢ λx. b : Πx : A. B     Γ ⊢ b a : B{x ↦ a}

Γ ⊢ k : Level< ℓ    Γ ⊢ A : 𝒰 k    Γ ⊢ b : ⊥
----------------    -------------------------
  Γ ⊢ ⊥ : 𝒰 k            Γ ⊢ abs b : A

--------------------    + reflexivity,  symmetry,
(λx. b) a ≈ b{x ↦ a}     transitivity, congruence
```

Now here are the typing rules involving universes and levels,
which rely on a meta-level notion of elements `i`, `j` with an order `· < ·`.
These elements embed into object-level universe levels via the constructor `lvl`.
The metavariables `k`, `ℓ` represent syntactic level expressions,
and `Level< ℓ` represents bounded levels strictly smaller than `ℓ`.
Universes `𝒰` then take a level expression `ℓ` instead of just a natural.

```
Γ ⊢ k : Level< ℓ        Γ ⊢ k : Level< ℓ                ⊢ Γ    i < j 
----------------    -------------------------    --------------------------
Γ ⊢ 𝒰 k : 𝒰 ℓ      Γ ⊢ Level< k : 𝒰 (lvl j)    Γ ⊢ lvl i : Level< (lvl j)

Γ ⊢ k₁ : Level< k₂    Γ ⊢ k₂ : Level< k₃    Γ ⊢ A : 𝒰 k    Γ ⊢ k : Level< ℓ
----------------------------------------    --------------------------------
           Γ ⊢ k₁ : Level< k₃                         Γ ⊢ A : 𝒰 ℓ
```

Universes, of course, continue to live in strictly larger universes.
Any `Level<` type, on the other hand, can live in any universe —
they don't stand for universes themselves,
but the set of labels pointing to each universe,
and so can be as big or as small as you like.
The introduction rule for `lvl` can be thought of internalizing the order `· < ·`,
while the other rule for levels can be thought of internalizing its transitivity.
The latter allows deriving judgements like `x : Level< (lvl 6) ⊢ x : Level< (lvl 9)`
to allow level variables to be used as if bounded by levels
larger than that they were declared with.

Finally, a cumulativity rule allows using a type at a larger universe level.
This is weaker than subtyping, since for instance a function
`f` of type `Πx : 𝒰 (lvl 9). B` cannot directly be assigned type `Πx : 𝒰 (lvl 6). B`:
function types aren't contravariant in the domain with respect to levels.
However, cumulativity allows eta-expanding `f`, namely that
`(λx. f x)` *can* be assigned type `Πx : 𝒰 (lvl 6). B`,
since the variable `x : 𝒰 (lvl 6)` can be assigned type `𝒰 (lvl 9)` to match `f`.

## Logical Relation

The semantic model of the type theory is a logical relation
inductively defined in impredicative Prop
which relates a type to a set of terms, i.e. a predicate on terms.
The inductive is parametrized over a semantic universe level
and an abstract relation for all lower levels.
The top-level relation is defined by well-founded induction on the level.
Below is a sketch of the logical relation,
omitting details about the impredicative encoding required for functions,
since the definition would otherwise not be strictly positive;
details can be found in @yiyunliu's paper.
Although the mechanization uses the notation `⟦A⟧ i ↘ P`,
I continue to also use the notation `a ∈ ⟦A⟧ᵢ` here for better intuition,
which represents `∃ P, ⟦A⟧ i ↘ P ∧ P a`.

```
j < k    ∃ P, ⟦A⟧ⱼ ↘ P                   a ⇒⋆ lvl i    i < j
----------------------    ---------    -----------------------
   A ∈ ⟦𝒰 (lvl j)⟧ₖ       b ∉ ⟦⊥⟧ₖ     a ∈ ⟦Level< (lvl j)⟧ₖ

∀ a ∈ ⟦A⟧ₖ, f a ∈ ⟦B{x ↦ a}⟧ₖ     A ⇒ B    a ∈ ⟦B⟧ₖ
-----------------------------    ------------------
      f ∈ ⟦Πx : A. B⟧ₖ                a ∈ ⟦A⟧ₖ
```

An important property when using this impredicative encoding
rather than induction–recursion is determinism:
If `⟦A⟧ i ↘ P` and `⟦A⟧ i ↘ Q`, then `P = Q`.
Because we're handling equalities between predicates,
proving determinism requires function extensionality and propositional extensionality.

The semantic universe levels are abstracted out via a typeclass
containing a type of levels, an order on the levels,
and further typeclasses for the following required properties on the order:

* Wellfoundedness, to construct logical relation;
* Transitivity, to ensure the logical relation is cumulative;
* Trichotomy, to prove determinism of the logical relation; and
* Cofinality, since every universe must have a type.

As such, the naturals are an appropriate instance of levels, as would be ordinals.

## Contents

* `level.lean`: Typeclass of cofinal, well-ordered levels.
* `syntactics.lean`: Syntax, substitution, contexts, and context membership.
* `reduction.lean`: Parallel reduction, substitution lemmas, confluence, and conversion.
* `typing.lean`: Definitional equality, context well-formedness, well-typedness, and inversion.
* `safety.lean`: Progress and preservation.
* `semantics.lean`: Logical relations stating semantic typing and well-formedness,
  along with important properties.
* `soundness.lean`: The fundamental theorem of soundness of typing —
  syntactic well-typedness implies semantic well-typedness.
  Consistency is proven as a corollary.
* `example.lean`: Partially-complete typing derivations for some example judgements
  involving terms with universe polymorphism.
