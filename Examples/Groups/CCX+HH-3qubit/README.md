# Three-qubit Toffoli–Hadamard circuits

This development follows Matthew Amy, Neil J. Ross and Scott Wesley,
[*A Sound and Complete Equational Theory for 3-Qubit Toffoli-Hadamard
Circuits*](https://arxiv.org/abs/2407.11152), using this repository's
`Word` and `Presentation` framework.

Words are in matrix-product order: the rightmost gate acts first.
The paper's wires 0, 1 and 2 are the most significant, middle and least
significant bits of the computational basis, respectively. Matrices
are exact, including global scalars, over ℤ[1/√2].

## Coverage

`Theorems.agda` is the entry point for the circuit transcription,
matrix interpretation, soundness, generator inverses and the normal
form of Lemmas 6.1 and 6.2, together with the repaired completeness and
group-presentation theorems below. Every corrected equation in Figures 4, 7
and 8 has an Agda matrix certificate. The relation contains 72
equations: 46 in Figure 4, 19 in Figure 7 and 7 in Figure 8.

`Permutation.agda` derives completeness for the permutation fragment
from the existing presentation of S₈. `CircuitLemmas.agda` replays
218 derivations from the authors' TIETZE2 files. `Frames.agda` and
`FrameWords.agda` define the reindexing calculus and the 106 one-,
two- and four-level generators on eight basis states. `TwoLevel.agda`
translates the relations of the existing dyadic two-level development
into the circuit theory; its finite instances are in `Transport/`
and `TransportCases/`.

`Repaired/Presentation.agda` proves completeness for exact matrix
equality and gives a full group presentation of L₈, the orthogonal
scaled dyadic matrices: matrices over ℤ[1/√2] with a common power of
1/√2 multiplying an integer matrix. Its interpretation is proved to
agree with the circuit's gate matrices, including global scalars.
`Theorems.agda` exports these results as `repaired-completeness` and
`repaired-presentation`. The relation includes the controlled-K
definition described below; completeness of the original 72 equations
alone is not asserted.

## Corrections and the retained K definition

`Errata.agda` contains exact matrix counterexamples to these printed
expressions, with the intended matrices:

- Equation (33): its last SWAP₀₂ must be SWAP₁₂. The authors' TIETZE2
  relation file already makes this correction.
- Section 5.6: the alias for the sign on basis state 0 requires X₂
  on both sides of CCZ, as well as X₀ and X₁.
- Section 5.5: under the paper's control-wire convention, the
  exchange of basis states 6 and 7 is CCX₀₁. CCX₁₂ exchanges 3 and 7.
- Equation (97): the exchange on its right side is X₁₃, rather than
  X₀₁.
- Equation (100): the matrices satisfy
  K₀₁₂₃ K₁₃₄₅ = K₂₃₄₅ K₀₁₂₄, rather than the printed commutation.

There is a further issue with the dyadic presentation. Section 5.5
uses the definition connecting the global K gate to controlled K
gates, but Figures 4 and 7 omit it:

```text
K₁₂ = NK · X₀ · NK · X₀
```

`MissingK.agda` constructs a matrix interpretation over ℤ/17ℤ that
satisfies all 65 corrected dyadic equations and separates this
equation. The model conjugates the Figure 4 matrices by I − J/4,
where J is the all-ones matrix, and keeps the intended CCZ and NK
matrices. It concerns the dyadic rules only; it does not establish
independence after adding the seven H₂ relations.

`Repaired/Syntactics.agda` retains this defining equation explicitly
alongside the corrected paper rules. `Repaired/Soundness.agda` checks
it in the intended exact matrix semantics. `Repaired/Encoding.agda`
gives the primitive encoding into the scaled two-level alphabet and
a syntactic proof that decoding an encoded circuit returns the
original circuit modulo these repaired relations.

The completeness proof first transfers the presentation of O₈(ℤ[1/2])
to the dyadic circuit fragment (`Repaired/DyadicCompleteness.agda`).
The nine remaining instances of the scaled two-level relations are
proved by normalizing their decoded circuits to even H₂ parity and
applying dyadic completeness (`HadamardRelations/`). This avoids using
the final circuit completeness theorem to prove its own premises.
`Repaired/TwoLevelScaled.agda` then lifts arbitrary two-level
derivations. Encoding, this lift, and the syntactic retraction prove
completeness; decoding and the existing surjectivity theorem for L₈
give the full presentation.

## Checking

Verification checkpoint: the original entry point, the imported
derivations, the missing-K countermodel, the repaired encoding and
repaired soundness, and both matrix bridges have passed Agda 2.8.0.
This includes all 32 shared evaluation modules and all 106 decoding
certificates. The assembled presentation and the newly exported
results are being checked.

Use Agda 2.8.0 and standard-library 2.4, with the registered EucDomain
dependency. Check separate entry points sequentially; do not run
Agda processes against the same interfaces concurrently.

```sh
agda Examples/Groups/CCX+HH-3qubit/Theorems.agda
agda Examples/Groups/CCX+HH-3qubit/CircuitLemmas.agda
agda Examples/Groups/CCX+HH-3qubit/MissingK.agda
agda Examples/Groups/CCX+HH-3qubit/Repaired/Encoding.agda
agda Examples/Groups/CCX+HH-3qubit/Repaired/Soundness.agda
agda Examples/Groups/CCX+HH-3qubit/Repaired/Presentation.agda
```

For the large finite translation, first check `Transport/r1a.agda`,
…, `Transport/r6a.agda` in separate processes, then `TwoLevel.agda`.
This frees each process's heap between relation families.

`bash Examples/Groups/CCX+HH-3qubit/tools/check.sh` runs the checks
sequentially with a compacting 3 GB heap, followed by `MainTheorems.agda`.
It writes durable logs under `local/ccxhh-3qubit-checks/`. A local
`tools/libraries-wsl` file can supply the library locations through
Agda's `--library-file` option when the WSL user has no global list;
the file is ignored because its paths depend on the machine.
From PowerShell, use `tools/check-wsl.ps1`, which invokes WSL directly.
The repository instructions' `/home/bonest/.local/bin/agda` path is not
present on this machine; `/usr/bin/agda` supplies Agda 2.8.0 here.

## Generated certificates and provenance

The Python programs in `tools/` are untrusted certificate generators.
The generated Agda modules use `--safe`, with no postulates or holes.
Matrix evaluations are shared, stored numerators; the circuit
certificates use the constructors of the repository's generated
monoid congruence. Searches and arithmetic performed by Python do
not contribute assumptions to the Agda theorems.

The `.rels`, `.derivs` and `step4.yaml` inputs come from
[`meamy/tietze`](https://github.com/meamy/tietze/tree/964b20f57657f10b5aa962f3ec703b99e41dd63b/examples/derivations),
at commit `964b20f57657f10b5aa962f3ec703b99e41dd63b`.
The accompanying MIT notice is retained in `tools/LICENSE-tietze`.
The downloaded paper and exploratory reference files are ignored.

The generators are split by purpose: `generate.py` transcribes and
checks the paper's equations; `import_tietze.py` replays the authors'
traces; `export_kb.py` emits checked permutation certificates from
saved search results; `generate_transport.py` builds the frame
relations and their finite instances; `generate_dispatchers.py`
assembles them into the two-level relation map;
`generate_encoding.py` emits the encoding retraction;
`generate_matrix_bridge.py` and `generate_decode_matrices.py` check
the matrix meanings of encoding and decoding;
`generate_hadamard_transport.py` emits the nine even-parity proofs
and their exhaustive dispatcher;
`generate_missing_k.py` and `generate_k_check.py` emit the two matrix
checks for the retained K equation.

Run `generate_transport.py` before `generate_dispatchers.py`, since
the latter refers to the finite instances emitted by the former.
