# Verified Generators and Relations for Qupit Clifford Operators

The `vqupit-pldi27` branch contains the [paper](vqupit/), the Agda
formalization it describes, and their transitive dependencies. It was
branched from `ten-completeness` at `3c12abee`.

## Contents

- [`vqupit/`](vqupit/) contains the manuscript, bibliography, figures,
  literate Agda snippets, generated LaTeX, and built PDF.
- [`MainTheorems.agda`](MainTheorems.agda) states the headline results:
  uniqueness of the symplectic normal form; the simplified symplectic
  presentation; the projective Clifford presentations; the exact Clifford
  presentation, with and without the extra scalar −1; and Figure 1 with
  its scalars. It also checks the structural-rule independence results,
  the symmetric-group example, and the generic constructions used in the
  paper. `Qudit-Clifford` supplies Figure 1's completeness and soundness.
- `Examples/` contains those developments and the supporting cyclic and
  trivial groups. `Word/`, `Presentation/`, `Circuit/`, `Normalization/`,
  and `ForStdlib/` contain the framework modules they depend on.

Unrelated papers, Lean developments, Agda examples, and unused modules
have been removed. The retained Agda modules are the import closure of
`MainTheorems.agda` and `vqupit/sections/*.lagda.tex`. Existing proof
modules are unchanged. The paper's figures and generated LaTeX are
included locally; their original source directories are not needed to
build it.

## Check the formalization

Use **Agda 2.8.0** and **standard library 2.4**. Register the standard
library's `standard-library.agda-lib` in `~/.agda/libraries`.
[`qupit.agda-lib`](qupit.agda-lib) includes the repository root and
depends only on `standard-library`; this branch does not need EucDomain
or any Git submodules.

From the repository root:

```sh
agda MainTheorems.agda
```

On Windows, use WSL (with Agda installed on its PATH):

```powershell
wsl --exec agda MainTheorems.agda
```

The exact qupit and scalar proofs can be memory intensive. A bounded
compacting heap can be used with `+RTS -M5G -c -RTS`. If a fresh check
runs out of memory, check the module it stopped on separately, then
rerun the root to reuse its interface.

## Build the paper

Install GNU Make, TeX Live with `acmart`, and `latexmk`, then run:

```sh
make -C vqupit
```

To regenerate every literate snippet before building:

```sh
make -B -C vqupit agda
make -C vqupit
```

The literate snippets are deliberately abbreviated and are checked with
`--only-scope-checking`. Check the actual proofs with `MainTheorems.agda`.
See [`vqupit/README.md`](vqupit/README.md) for manuscript details;
its source-history notes refer to the larger repository before this
branch was extracted.
