# Presentation Lib — structure

## Notations
Numeral and successor patterns shared by the whole library.

## Word
- Base — the free monoid `Word X`, `(f *)`, `(h **)`
- Properties — functor fusion laws, decidable equality

## Presentation
- Base — the congruence closure `_≈_` of a raw relation `_===_`
- Properties — setoid/monoid structure, associativity solvers, powers
- Definitions — `_IsPresentationOf_` and friends; soundness / completeness between setoids, i.e. presentation of a sub-setoid (`module SubPresentation`)
- GroupLike — inverses and the group of words
- Morphism — homo/mono/isomorphism builders for `(f *)`
- Reidemeister-Schreier — the injectivity engine
- Construct — products: direct, semidirect, n-fold, sugar, amalgamated
- Groups — concrete presentations: Cyclic, Sn, SnD, Trivial

## Circuit
- Base — wire-indexed gates, circuits, and structural lifting rules

## Normalization
- Base — normal-form witnesses, `UniqueNormalForm`, `by-normalization`
- CosetNF — coset normal forms, coset tables, coset towers

## Examples

### Groups/Symmetric
`Theorems.agda` collects the main properties of the presentation.  Its
purpose is 1) to display the major properties and 2) to separate
statements from proofs: definitions used in statements are imported
and opened, while the properties used in the proofs are imported
qualified but not opened.  Similarly for other files named Theorems.

### Amalgamations
Complete relation sets illuminate group structure.  These examples
show a group is an amalgamated product of two of its subgroups using
complete relations: the qubit and qutrit Clifford+T gate sets, and
U₃(ℤ[½,i]).
