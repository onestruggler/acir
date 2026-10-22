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
into the circuit theory, each of its 21 relation families once, at
symbolic indices: every generator is a centre (`m0`, `t01` or `NK`)
conjugated by a Coxeter word, and by the frame lemma of
`Examples/Groups/Symmetric/CoxeterFrames` that conjugate depends only
on where the word sends the centre's states, so a relation follows
from its standard instance (the argument of `CCX+HH-3qubit-opus`'s
`Decode`). The tables of Coxeter words in `FrameWords` (`fM`, `fX`,
`fK`, `fK′`) are related to those frames by one evaluated check per
table (`okM`, `okX`, `okK`). This replaces the 2,123 finite instances,
their dispatchers and the frame moves that were checked one by one:
577 modules and about 440 s of checking, against 3 s.

Decoding preserves the matrix (`Repaired/DecodingMatrices`): the basic
letters (-1)_[0], X_[x,x+1] and K_[0,1,2,3] have matrix certificates
(`DecodeMatrices/`), and every other letter is a basic one conjugated
by adjacent X's (`CCX+HH-TwoLevel`'s `Conjugation.decompose`), which
both readings respect — the two-level one by the soundness of Table 1,
the circuit one by `TwoLevel.decode-cong` — as in
`CCX+HH-3qubit-opus`'s `dec-sem`. It replaces 97 certificates and 722
of their 763 matrix evaluations.

`Repaired/Presentation.agda` proves completeness for exact matrix
equality and gives a full group presentation of L₈, the orthogonal
scaled dyadic matrices: matrices over ℤ[1/√2] with a common power of
1/√2 multiplying an integer matrix. Its interpretation is proved to
agree with the circuit's gate matrices, including global scalars.
`Theorems.agda` exports `repaired-soundness`, `repaired-completeness`
and `repaired-presentation`. The relation includes the controlled-K
definition described below; completeness of the original 72 equations
alone is not asserted.

### Circuits over `Circuit.Base`

`Circuits/` restates the presentation over the repository's circuit
syntax (`Circuit.Base`): the gates X and H on one wire, CX (control on
the upper wire) and K = H ⊗ H on two, CCX (target on the top wire),
NK = K_[0,1,2,3] and CCZ on three, placed on their wires by the shift
_↑, with qubit 2 on wire 0 and qubit 0 on wire 2. Each of the paper's
letters is a circuit of the same name, the ones Figure 4 defines by
their definitions, so that the other relations, and the definition of
K, are rules word for word; the four commutations of gates on disjoint
wires among them ((26), (27), (102), (103)) are the structural rules
of `Circuit.Base`, and one rule places H on wire 1 (the paper's H₁ =
K₁₂ H₂). `Circuits/Iso.agda` reads a gate as the paper's letter and
proves the reading a group isomorphism on three wires — the
commutations of gates on disjoint wires that the paper does not state
come from its completeness — and `Circuits/Presentation.agda`
concludes that the circuits present L₈. `tools/gen_circuits.py`
writes `Circuits/Syntactics.agda` and `Circuits/Iso.agda` from
`Syntactics.agda`.

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

All 198 Agda modules in this directory pass Agda 2.8.0 with
standard-library 2.4, including the assembled presentation, its public
exports, the original circuit lemmas, the missing-K countermodel and
the standalone audits. The public entry point, full-directory audit
and `MainTheorems.agda` also pass through WSL from the Windows working
tree. This includes the shared evaluation modules, the nine
decoding certificates of the basic letters and both matrix bridges.
`TwoLevel.agda` covers all 21 relation families at symbolic indices.
Dyadic completeness, the scaled two-level map and its nine Hadamard
certificates all pass. The repository-wide `MainTheorems.agda`
regression check also passes.

Regenerating the frame words, the permutation certificates, the
decoding matrices and the Hadamard relations reproduces them exactly.

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

`bash Examples/Groups/CCX+HH-3qubit/tools/check.sh` checks the four
roots that reach every module of the directory but `Circuits/` —
`CircuitLemmas`, `MissingK`, `Theorems` and `StrictMatrix` — and
`Circuits/Presentation`, which reaches those, sequentially with a
compacting 8 GB heap, followed by `MainTheorems.agda`: about three
minutes from scratch, `Theorems` 94 s of them. (It was about
twelve minutes, `Theorems` eleven with a peak of 6.2 GB, while the
relations were transported and the decoding checked instance by
instance; and
about two hours when the relation families, the decoding certificates
and the Hadamard relations were roots of their own, some 200 processes
that each loaded the same interfaces again.)
It writes durable logs under `local/ccxhh-3qubit-checks/`. A local
`tools/libraries-wsl` file can supply the library locations through
Agda's `--library-file` option when the WSL user has no global list;
the file is ignored because its paths depend on the machine.
From PowerShell, use `tools/check-wsl.ps1`, which invokes WSL directly.
Its `-Heap` option, or `AGDA_HEAP` for `check.sh`, changes the bounded
heap.
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
saved search results; `generate_frames.py` writes the frame words
and their tables, `generate_base_frames.py` the classical gates as
Coxeter words; `generate_encoding.py` emits the encoding retraction;
`generate_matrix_bridge.py` and `generate_decode_matrices.py` check
the matrix meanings of encoding and decoding;
`generate_hadamard_transport.py` emits the nine even-parity proofs
and their exhaustive dispatcher;
`generate_missing_k.py` and `generate_k_check.py` emit the two matrix
checks for the retained K equation; `gen_circuits.py` writes the
circuit presentation (`Circuits/`).

Run `bundle.py` after the generators: they write one module per
certificate, and `bundle.py` merges them into chunk modules (below). On Windows set
`PYTHONUTF8=1`: `import_tietze.py` reads its inputs in the default
encoding.
`export_kb.py --permutation` writes `PermProofs/`; without the flag it
writes `Proofs/`, of which the repository keeps the 22 modules in use.

## Typechecking cost

The certificates are small and many, and the generators write them so
that they stay cheap to check and to load (the repository's
`typecheck-efficiency.md` has the measurements):

- The relations of Table 1 are transported generically (`TwoLevel`,
  above), one argument per relation family, where 2,123 finite
  instances, their dispatchers and some 2,000 frame moves and
  permutation checks used to be certificates of their own: 577 modules
  and about 440 s of the directory's 624 s of checking.
- The 882 remaining one-line certificates (`PermProofs`, `Tietze`,
  `Proofs`) are nested modules of 37 chunk modules (`B000`, …), each
  under its old name, and a module that used one imports it from its
  chunk (`open import ….PermProofs.B021 using (module braid0)`).
  `tools/bundle.py` does this after the generators. Agda pays for a
  module apart from its contents — it is loaded, merged into the state
  of every module that imports it, and has an interface of its own —
  and with the transport certificates the directory was 8279 modules,
  910 once bundled.
- A certificate imports `Kit` restricted to the names it uses
  (`import Kit as K using (…)`, then `open K`; `generate.py`'s `kit`).
  An interface records the whole scope of every module its module
  imports, so certificates that opened Syntactics, Frames, FrameWords
  and Engine had 50–65 kB interfaces for one line of proof, against
  9–15 kB.
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
  `Repaired/TwoLevelScaled` supplies, so that each loads only what
  that comparison does not need.
- The decoding is certified on the nine basic letters only and
  carried to the others along `Conjugation.decompose` (above): its 106
  certificates, 763 matrix evaluations and a dispatcher by first index
  were about 100 s.
