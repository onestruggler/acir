# qupit — Agda formalisation

Agda formalisation of group presentations, normal forms, and complete
relation sets for multi-qudit Clifford circuits.

## Versions

| Component            | Version |
| -------------------- | ------- |
| Agda                 | 2.8     |
| Agda standard library| 2.4     |


The library configuration is in [`qupit.agda-lib`](qupit.agda-lib): it
includes the repository root (`.`) and depends on `standard-library`.

## Typechecking

`MainTheorems.agda` restates the headline theorems of this branch, with
full types, and reaches through them everything their proofs rest on:

```bash
agda MainTheorems.agda
```

It states

- **the qupit chain, read modulo scalars**: the symplectic normal form
  is unique (`unique-nf`); the simplified symplectic rules present
  Sp(2n, ℤ/pℤ) (`simplified-presentation`); and the V1 Clifford rules
  and the paper's Figure 1 rules, read modulo scalars, present
  Pauli(n) ⋊ Sp(2n, ℤ/pℤ) (`v1-presentation`, `clifford-presentation`);
- **the scalars restored**: the exact rule set, the scalar ω with its
  one correction ω^((p²−1)/8), presents the central extension of that
  group by ⟨ω⟩ (`exact-clifford-presentation`); with −1 adjoined it
  presents that extension times ⟨−1⟩ (`clifford±-presentation`); and
  the paper's Figure 1 itself — its sixteen rules C0–C15 over −ω, H, S,
  CZ, with the Legendre symbols and phases of its derived generators —
  presents the same group (`figure1-presentation`, the paper's
  Theorem 4.10 against the constructed group);
- **the structural rules are independent** (`Structural-Theorems`):
  none of cong↑, comm₁, comm₂ and ω↑=ω follows from the others, and a
  scalar's centrality, a theorem of them, needs scalars to commute
  with one another.

Every result is parametric in the odd prime p, the width n and a
primitive root g, and every file is checked under `--safe`: there are
no postulates and no holes.  The two "glue facts" — that the
constructed groups are the groups of unitaries the gates generate — are
classical and not formalised.  From scratch the root takes about half
an hour, most of it the symplectic chain and `Clifford/Qupit/`.

This is the `qupit` branch, so the root covers only that chain.  The
library's other developments are still in the tree but are not reached
from it: the symmetric, trivial and cyclic groups, the wreath product,
the Clifford+T and U₃(ℤ[½,i]) amalgamations, the qubit Clifford groups
(`Clifford/Qubit/`, `ProjectiveClifford/Qubit/`), Real-Clifford+CH,
CNOT-dihedral, and `ProjectiveClifford/Qupit/Simplified-V2`.  Check
those on their own roots if you touch them.

## Papers

- [`vqupit/`](vqupit) — *Verified Generators and Relations for Qupit
  Clifford Operators*, the long version (`acmart`, 28 pages with the
  references).  Its sections that quote Agda are literate Agda files,
  scope-checked against this library: `make` there runs Agda on them,
  then `latexmk`.
- [`vqupit-short/`](vqupit-short) — the five-page version of the same
  paper (12 pages with the references and appendices); `make` there
  needs only `latexmk`.

Both directories carry a built `main.pdf` and a README with the build
details.
