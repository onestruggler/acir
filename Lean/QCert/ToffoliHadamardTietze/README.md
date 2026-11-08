# Amy, Ross, Wesley (2024): a partial translation of `CCX+H-3qubit-Tietze`

A Lean translation of the first modules of the Agda development
`Examples/Groups/CCX+H-3qubit-Tietze/`, module for module, with the same
names, definitions and certificates.  It stops before the decoding of Li,
Ross and Selinger's generators (`TwoLevel`) and proves no main theorem; it
exists to compare the two assistants on the same text (`pldi/compare/part.py`,
the second Toffoli–Hadamard row of the paper's Figure 6(a)).

## What is translated (46 modules, all checked)

| Agda (`CCX+H-3qubit-Tietze/`) | Lean (`QCert/ToffoliHadamardTietze/`) | |
| --- | --- | --- |
| `Syntactics` | `Syntactics` | the 26 letters and the 72 equations of Figures 4, 7 and 8 |
| `Engine`, `Kit` | `Engine`, `Kit` | the replay steps (`under`, `by_assoc_and`), under the Agda's names |
| `Proofs/B000` | `Proofs/B000` | 22 completion lemmas (`gen/export_kb.py`) |
| `Tietze/B000`–`B008`, `CircuitLemmas` | the same | the 218 derivations of the authors' TIETZE2 files (`gen/import_tietze.py`) |
| `PermProofs/B000`–`B026` | the same | 642 certificates of the permutation fragment (`gen/export_kb.py --permutation`) |
| `Permutation` | `Permutation` | the Coxeter relations for `X_[k,k+1]` (`gen/generate_permutation.py`) |
| `Frames`, `States` | the same | Coxeter words as circuits; checks on the eight states |
| `FrameWords` | `FrameWords` | the 106 decoded generators and their tables (`gen/generate_frames.py`) |
| `GatePermutations` | `GatePermutations` | the classical gates as Coxeter words (`gen/generate_base_frames.py`) |

The generators in `gen/` are ports of the Agda's `tools/`: they read the
same inputs from the Agda folder (the authors' `.rels` and `.derivs`
files, the saved search results, and the relations of the Agda's
`generate.py`, imported for its data) and write Lean.  The certificates are
grouped into the Agda's chunk modules (read off the Agda chunks), so that the
two correspond file for file.  Run them from `gen/` in the order
`export_kb.py`, `import_tietze.py`, `export_kb.py --permutation`,
`generate_permutation.py`, `generate_frames.py`, `generate_base_frames.py`
(with `PYTHONUTF8=1` on Windows).

## Deviations

* Words are the framework's `FreeMonoid`; a certificate's step closes the
  Agda's `by-assoc-and … Eq.refl Eq.refl` with `rfl`, and the chunks with
  words of some forty letters raise `maxRecDepth`.
* The Agda reads Coxeter words as circuits of the repository's presentation
  of `S₈` and transfers its completeness; the Lean library has none, so
  Coxeter words are the lists of `CoxeterFrames` (the translation of the
  Agda's shared `Symmetric/CoxeterFrames`, imported from
  `QCert.ToffoliHadamardRS`), and `Permutation.cox` gives the Coxeter
  relations that its completeness takes.  States are natural numbers below
  `8` (the Agda's `Fin 8`).

## Not translated

`TwoLevel` (Table 1 for the decoded circuits), `PrimitiveFrames`, `Core`,
`Normalization`, `Invertible`, `GroupLike`, the semantics and its
certificates (`GateMatrices`, `Interpretation`, `Evaluation`, `Checks`,
`Soundness`, `Errata`, `Matrix`, `StrictMatrix`), `Repaired/`,
`HadamardRelations/`, `DecodeMatrices/`, `FrameEvaluation/`, `MissingK/`,
`Circuits/`, `DOmega`, `MainTheorem` and `Theorems`: 157 of the 203 Agda
modules.

## Typechecking

`./check.sh QCert/ToffoliHadamardTietze/GatePermutations.lean
QCert/ToffoliHadamardTietze/CircuitLemmas.lean QCert/ToffoliHadamardTietze/States.lean`
builds all 46 modules, about five minutes (the 27 permutation chunks
3 min 40 s).  The folder is not imported by `QCert.lean`.
