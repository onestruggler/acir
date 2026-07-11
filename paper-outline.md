Normal forms and complete relations for circuits in Agda

# Abstract

# Introduction

  Emphasizing that completeness proofs involves a lot of
computations. By formalizing it in Agda, we get correctness
guarantee. E.g., Paper by Alexandre Clément, A Complete Equational
Theory for Real-Clifford+CH Quantum Circuits involves almost 300 pages
handwritten proofs of completeness, which should and can by verified
in this framework.



## Contributions

   0. An Agda library for reasoning circuit normal forms and complete
   relations.

   1. Inductively defined circuit for easy normalization and
   completeness proofs.

   2. 7 examples formalized, including serveral from research papers
   (one is published this year)

   3. Generalize the definition of group amalgamation to monoids, just
   like what Bian and Selinger did for generalizing the
   Reidemeister-Schreier method for groups to for monoids.

   4. new theorems that the stdlib lacks are introduced when
   fomalizing the semantic side.

## Example: Permutations

## Related work

   mentioning previous work of Selinger and Bian only works on the
   syntactic side (they verify two set of relations are equivalent,
   never mentions their semantics): - https://arxiv.org/abs/2306.08530
   - https://arxiv.org/abs/2204.02217



### Related tools

    https://www.mathstat.dal.ca/~xbian/LafontLP/
    https://www.mathstat.dal.ca/~xbian/qupit/index.php

# Preliminary

   The normal form given by a subgroup chain / stabilizer chain via
   transversals (and cite Sims/Schreier–Sims), noting the mixed-radix
   "digit expansion" analogy — each coset index is a digit in a
   group-theoretic positional system. Specialize to circuit setting,
   i.e., the subgroup chain is {Cir k | 0 <= k <= n, k is natural
   number}, since Cir k < Cir (k + 1).



# Libary Design

## Design of Circuit

   Inductively defined Circuit, and Inductively defined circuit
   realtions ease the formalization. Careful state such
   design. Prepare Examples showing correspondence between circuit
   code and tizk drawing of circuit.

## NFProperty

   We have serveral versions of NormalForm property; mention the one
   require nf-injective is strictly weaker than the one requires a
   section and a retraction in the constructive setting.

# Examples

  List all proved presentations. To be precise, list all (R
  IsPresentationOf G) records in the repo, including the relations R
  and group G and also premises. Same for all the NormalForm and
  UniqueNormalForm record.

  Use the fancy name signed permutations/hyperoctahedral group for
  SnD.  (formalize Lamplighter group if we have time)
  

# Conclusion and future work

# Acknowledgement

  We have used Claude to help with refactoring the code base
  \cite{qupit-code} to the current. We have used Claude to write this
  paper according to our paper outline \cite{paper-outline} (later
  checked and revised by us).

# References

