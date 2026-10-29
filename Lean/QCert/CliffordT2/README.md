# Two-qubit Clifford+T (Bian–Selinger, QPL 2022)

X. Bian and P. Selinger, *Generators and relations for 2-qubit Clifford+T
operators*, QPL 2022, arXiv:2204.02217.  Table 1 of qcert.tex: "two-qubit
Clifford+T, sub-presentation in U₄".

## Statement

* `Syntax.lean`: the generators 𝒳 = {ω, H₀, H₁, S₀, S₁, T₀, T₁, CZ} of
  Theorem 2.1 and the relations (C1)–(C20) of Figure 1, one constructor per
  printed relation (indexed by `i : Fin 2` where the figure says
  "i ∈ {0, 1}"), with the abbreviations of Figure 2 (`W.X`, `W.CX`,
  `W.CXw`, `W.CH`, `W.CHw`, `W.Tdg`, `W.Sdg`).  Words are in the order of
  matrix multiplication, as in the paper.  Where Figure 1 draws two gates on
  different qubits at the same horizontal position, the order is that of the
  authors' `Generator.agda`.
* `Semantics.lean`: H = (1/√2)[[1,1],[1,-1]], S = diag(1, i), T = diag(1, ω),
  CZ = diag(1,1,1,-1); `A₀ = A ⊗ I`, `A₁ = I ⊗ A` (`tensor`), the scalar ω
  as ω I.  A 4 × 4 matrix is indexed by `Fin 4`, `|q₀ q₁⟩` at index
  `2 q₀ + q₁` (qubit 0, the paper's top wire, is the most significant digit).
  Matrices are written over ℚ(ω) and read in ℂ; `sem` lands in `U(4)`,
  `semU` in `U₄(ℤ[1/√2, i])`.
* `Theorem.lean`: `theorem_2_1 : IsSubPresentationOf Rel sem` and
  `theorem_2_1_U : IsSubPresentationOf Rel semU`.

## Proofs

* Soundness of every relation (`Soundness.lean`) by `decide +kernel`, with a
  column-by-column evaluator over ℤ[ω] and powers of 1/√2 (`ZOmega.lean`,
  `Eval.lean`): each relation in about a second.  `grouplike`: every
  generator has an inverse modulo the relations.
* Completeness (Section 5 of the paper, `Completeness.lean`), as in the
  paper and the authors' code:
  - `ReidemeisterSchreier.lean`: Theorem 4.3 (Reidemeister–Schreier for
    monoids), proved in general.
  - `Translation.lean`: the translation `f` of Section 5.1 into Greylyn's
    generators respects the interpretation.
  - Greylyn's Theorem 4.1 is imported from `QCert.Greylyn.presentation`
    (another folder).
  - `Simplified.lean`, `SimplifiedGreylyn.lean`: the authors' five-generator
    form (S1)–(S19) of Greylyn's presentation; all 123 instances of Greylyn's
    relations are derived from (S1)–(S19) by normalization and basis changes,
    as in the authors' `Greylyn-Simplified.agda`.
  - `Cosets.lean`: the two cosets `I`, `Ω` and the coset action `h` of the
    authors' `Completeness.agda`; the cosets reached are decided.
  - `Equations.lean`: the 46 equations that are hypotheses (a) and (b) of the
    Reidemeister–Schreier theorem (the authors' `Equation1.agda` …
    `Equation46.agda`).
  - `Rewrite.lean`: checked rewriting; certificates (lists of rewriting
    steps, packed into one number) found outside Lean are replayed by
    `decide +kernel`.

## Certificates

The 46 equations are proved by rewriting certificates, found outside Lean
and replayed by the kernel (`decide +kernel`); only the replay is trusted.

* `Rewrite.lean`: rules (`Rule Γ`: an equation between lists of letters
  with its derivation), rewriting steps `(position, rule, direction)`,
  their replay on lists and its soundness.
* `FastRewrite.lean`: the same replay on words coded as numbers (a word
  `a₀ a₁ …` is `κ a₀ + 16 κ a₁ + ⋯`, `κ` a coding of the letters by
  `1 … 15`), each step a few operations on numbers that the kernel
  evaluates eagerly; steps are packed 25 bits each into numbers, in chunks
  of 2000 (`runChunks`, `derivable_of_chunks`, `Rule.byChunks`), with the
  soundness proved once (`runFast_sound`, from the arithmetic of the coding).
* `Cert/Code.lean`: the coding of the eight letters.
* `Cert/Axioms.lean`: the relations of Figure 1 as rules.
* `Cert/Clifford.lean`: normal forms of the two-qubit Clifford group by a
  stabilizer chain `⟨ω⟩ ⊂ ⟨ω,S₀⟩ ⊂ ⟨ω,S₀,H₀⟩ ⊂ ⟨…,S₁⟩ ⊂ ⟨…,H₁⟩ ⊂ ⟨…,CZ⟩`,
  each coset-table entry `r x → λ r'` a rule proved from the relations
  (the last table, the 20 cosets of the local Clifford group, by coset
  enumeration with proofs: every entry deduced from a relator, or found by
  a search through partial normal forms).
* `Cert/Rotations.lean`: the Pauli rotations of Section 4.3,
  `R(P) = C_P T₀ C_P⁻¹`: a Clifford letter passes a rotation
  (`R(P) x = x R(x†Px)`), `R(-P) = E_P R(P)`, `R(P)² = C_P S₀ C_P⁻¹`,
  commuting rotations commute, `T₁ = R(I⊗Z)`; `lemma-rel-A` and
  `lemma-rel-B` of the authors' code (the squares of the words of (C18) and
  (C19) are trivial); and the local lemma of the authors' Equation 46.
* `Eqs/Part00.lean` … `Eqs/Part12.lean`: the 46 equations (870 000 rewriting
  steps in all, the longest 286 000; a long certificate is cut into lemmas of
  at most 10 000 steps between explicit intermediate words, which keeps
  each kernel check within a few gigabytes).  Both sides of
  each are brought to the same normal form `C · R(P₁) ⋯ R(Pₙ)`: a Clifford
  normal form followed by positive Pauli rotations in the lexicographic
  normal form of their commutation trace.  For Equations 21, 28, 30, 43, 44
  and 46 the two sides have different such forms, and, as in the authors'
  proofs, (C18), (C19) and (C20) are applied at the places their
  `Equation21/28/30/43/44/46.agda` apply them (`lemma-rel-A`,
  `lemma-rel-B`, `rel-C`); between those places, normal forms agree.

The generating scripts are in `gen/` (Python).  `gen/README.md` says:

- which script writes which module (`Cert/*`, `Eqs/*`, `Equations.lean`,
  `SimplifiedGreylyn.lean`);
- where to get the authors' ancillary files they read (by URL and
  SHA-256);
- that a regeneration from scratch reproduces the committed modules byte
  for byte.

## Remaining `sorry`s

None.  The completeness proof uses Greylyn's Theorem 4.1 through
`QCert.Greylyn.presentation` (folder `QCert/Greylyn/`), and
`#print axioms` reports `[propext, Classical.choice, Quot.sound]` for
both `theorem_2_1` and `theorem_2_1_U`.

## Building

The equation files take about 9 minutes in all (`Eqs/Part09`,
`Part10` and `Part12` 1.5 to 2.5 minutes each; they were 30 minutes
before the rules were compiled, see "Typechecking cost"), about 2 GB
resident each; the rest of the folder a few minutes.  Lemmas of 60 000 steps
needed over 7 GB, hence the cut at 10 000.

## Paper errors

None found: every relation of Figure 1 holds (decided), every translated
Greylyn relation is derivable, and all 46 equations are proved.

## Typechecking cost

The certificate modules are kernel-bound: `by decide +kernel` makes the
kernel replay the packed steps, and the kernel pays for every unfolding
and almost nothing for arithmetic on literals (GMP).  `FastRewrite.lean`
is written for that: the rules are compiled once to the codes and lengths
of their sides (`compileRules`), where the first version recomputed
`enc κ ρ.lhs` and `ρ.lhs.length` at every step; the rule is looked up by
primitive recursion (`nthC`), where `rules[i]?` goes through `List.length`,
a `Decidable` test and `brecOn`; and the tests are `Nat.beq`/`Nat.ble`
under `bif` (`replaceB`), where an `if` on a `Nat` proposition unfolds a
`Decidable` instance.  Together, on the 5 147 steps of `Eqs/Part04`, the
kernel time went from 4.3 s to 1.3 s, and `Eqs/Part12` (290 000 steps)
from 646 s to 139 s in a full build.  A balanced tree of rules, built
lazily from the list, was slower than the list (4.2 s): the kernel's
cache of weak head normal forms serves a list of compiled rules well, and
the tree's construction costs more than the depth it saves.  Elaboration
is about 20 s for `Part12`, mostly the 145 numerals of 15 000 digits.
