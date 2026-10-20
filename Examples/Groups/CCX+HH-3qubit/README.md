# Three-qubit Toffoli–Hadamard circuits

This development follows Matthew Amy, Neil J. Ross and Scott Wesley,
[*A Sound and Complete Equational Theory for 3-Qubit Toffoli-Hadamard
Circuits*](https://arxiv.org/abs/2407.11152), using this repository's
`Word` and `Presentation` framework.

[ERRATA.md](ERRATA.md) records the corrections, repeated occurrences,
matrix witnesses and the completeness issue caused by omitting `r_K`.

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
and `TransportCases/`. Wide dispatchers use `TransportChunks/` to
split the index choices into modules with at most four remaining
indices; the public `translate` functions retain their original types.

`Repaired/Presentation.agda` proves completeness for exact matrix
equality and gives a full group presentation of L₈, the orthogonal
scaled dyadic matrices: matrices over ℤ[1/√2] with a common power of
1/√2 multiplying an integer matrix. Its interpretation is proved to
agree with the circuit's gate matrices, including global scalars.
`Theorems.agda` exports `repaired-soundness`, `repaired-completeness`
and `repaired-presentation`. The relation includes the controlled-K
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
- Section 5.5: the prose reverses the control states of
  K_[0,1,2,3] and its conjugate by X₀; they act when qubit 0 is 0
  and 1, respectively.
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

All 8,229 Agda modules in this directory pass Agda 2.8.0 with
standard-library 2.4, including the assembled presentation, its public
exports, the original circuit lemmas, the missing-K countermodel and
the standalone audits. The public entry point, full-directory audit
and `MainTheorems.agda` also pass through WSL from the Windows working
tree. This includes all 32 shared evaluation modules,
all 106 decoding certificates and both matrix bridges.
The six-index `Transport/r2c.agda` dispatcher, including its 420 cases,
passes with a compacting 3 GB heap. The complete `TwoLevel.agda` map
covers all 21 relation families and their 2,123 finite instances.
Dyadic completeness, the scaled two-level map and its nine Hadamard
certificates all pass. The repository-wide `MainTheorems.agda`
regression check also passes.

Regenerating the finite transports, dispatchers, decoding matrices
and Hadamard relations reproduces all 2,648 corresponding files exactly.

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
The prefix modules bound the size of each coverage check as well:
the four- to eight-index tables are not checked as one large case
analysis.

`bash Examples/Groups/CCX+HH-3qubit/tools/check.sh` runs the checks,
including the standalone audits, sequentially with a compacting 8 GB
heap, followed by `MainTheorems.agda`.
It writes durable logs under `local/ccxhh-3qubit-checks/`. A local
`tools/libraries-wsl` file can supply the library locations through
Agda's `--library-file` option when the WSL user has no global list;
the file is ignored because its paths depend on the machine.
From PowerShell, use `tools/check-wsl.ps1`, which invokes WSL directly.
Its `-Heap` option, or `AGDA_HEAP` for `check.sh`, changes the bounded
heap. Individual relation families can be checked with 3 GB; the
assembled presentation imports all families in one process.
The PowerShell supervisor retries interrupted runs from the interfaces
already saved on the Windows filesystem.
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
`export_kb.py --permutation` writes `PermProofs/`; without the flag it
writes `Proofs/`, of which the repository keeps the 22 modules in use.

## Typechecking cost

The certificates are small and many, and the generators write them so
that they stay cheap to check and to load (the repository's
`typecheck-efficiency.md` has the measurements):

- A certificate imports `Kit` or `FrameKit` restricted to the names it
  uses (`import Kit as K using (…)`, then `open K`; `generate.py`'s
  `kit`). An interface records the whole scope of every module its
  module imports, so certificates that opened Syntactics, Frames,
  FrameWords and Engine had 50–65 kB interfaces for one line of proof;
  now 9–15 kB, the folder's interfaces 350 MB rather than 595 MB.
  `Kit` and `FrameKit` are separate because Frames imports the
  permutation certificates, which import `Kit`.
- The matrix evaluations (`Evaluation`, `FrameEvaluation`,
  `MissingK/Evaluations`) come in chunks of 16–24, each importing from
  the earlier chunks only the names it uses (`evaluation_chunks`): a
  matrix literal has some 250 parenthesised subterms, and Agda's
  operator parser looks every name in scope up for each of them. A
  product over ℤ[√2] is decided by one boolean on the sparse product,
  and each `Eq.cong₂ mulM` step gives its matrices, which left to
  unification made Agda unfold both readings.
- The nine Hadamard relations take the comparison by dyadic
  completeness as a module parameter (`Repaired/Even.FromEven`), which
  `Repaired/TwoLevelScaled` supplies: each loads about 1100 interfaces
  rather than all 7900.
- The four-level decoding certificates are dispatched by first index,
  one module each (`Repaired/DecodingLetters`), and so are the
  four-index transport tables (`TransportChunks/r1c`, `r2a`, `r4a`–`r4c`;
  `r2a` was 1437 clauses in one function, 24 s).
