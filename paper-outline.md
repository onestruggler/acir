Normal forms and complete relations for circuits in Agda

# Abstract

# Introduction

  Emphasizing that completeness proofs involves a lot of
computations. By formalizing it in Agda, we get correctness
guarantee. E.g., Paper by Alexandre Clément, A Complete Equational
Theory for Real-Clifford+CH Quantum Circuits involves almost 300 pages
handwritten proofs of completeness, which should and can by verified
in this framework.

## Example: Permutations

## Related work

   mentioning previous work of Selinger and Bian only works on the
   syntactic side (they verify two set of relations are equivalent,
   never mentions their semantics): - https://arxiv.org/abs/2306.08530
   - https://arxiv.org/abs/2204.02217



### Related tools

    https://www.mathstat.dal.ca/~xbian/LafontLP/
    https://www.mathstat.dal.ca/~xbian/qupit/index.php

# Libary Design

## NFProperty

   We have serveral versions of NormalForm property; mention the one
   require nf-injective is strictly weaker than the one requires a
   section and a retraction in the constructive setting.

# Examples

# Conclusion and future work

# Acknowledgement

  We have used Claude to help with refactoring the code base
  \cite{qupit-code} to the current. We have used Claude to write this
  paper according to our paper outline \cite{paper-outline} (later
  checked and revised by us).

# References

