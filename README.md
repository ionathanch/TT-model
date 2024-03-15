# Mechanization of consistency

This mechanization has been checked with Agda 2.6.4.3 using agda-stdlib 2.0.
The top-level file can be checked by `agda consistency.agda`.

## Axioms

The only axiom used is function extensionality,
which is located in the `accext` module of `accessibility.agda`
as private postulates (one for an implicit and one for an explicit domain).
Function extensionality is only used to prove
mere propositionality of the accessibility predicate,
which in turn is only used to prove `accU` in `semantics.agda`.

## Contents

Most of the modules are parametrized over an abstract `Level`
and its strict transitive order,
only to be instantiated at the very end by the naturals.

* `common.agda`: Reëxports all the necessary agda-stdlib modules,
  and defines common definitions.
* `accessibility.agda`: The accessibility predicate and its mere propositionality.
* `syntactics.agda`: Syntax, substitution, contexts, and context membership.
* `reduction.agda`: Parallel reduction, substitution lemmas, confluence, and conversion.
* `typing.agda`: Definitional equality, context well-formedness, and well-typedness.
* `semantics.agda`: Logical relations stating semantic typing and semantic context formation,
  along with important properties.
* `soundness.agda`: The fundamental theorem of soundness of typing —
  syntactic well-typedness implies semantic well-typedness.
* `consistency.agda`: Strict order on the naturals, well-foundedness of the naturals
  with respect to its strict order, and logical consistency using the naturals as levels.

## Statistics

```
github.com/AlDanial/cloc v 1.98  T=0.01 s (654.7 files/s, 88706.0 lines/s)
--------------------------------------------------------------------------------
File                              blank        comment           code
--------------------------------------------------------------------------------
reduction.agda                       46             11            223
syntactics.agda                      42             21            181
semantics.agda                       38             20            178
typing.agda                          14             20            117
soundness.agda                        3              0             78
consistency.agda                     12              2             44
accessibility.agda                    4              0             18
common.agda                           1              0             11
--------------------------------------------------------------------------------
SUM:                                160             74            850
--------------------------------------------------------------------------------
```
