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

`Cert/Axioms.lean`, `Cert/Clifford.lean` and `Cert/Rotations.lean` are
rewriting rules, each proved by a packed certificate checked with
`decide +kernel`: the relations of Figure 1, the coset tables of a
stabilizer chain for the two-qubit Clifford group (normal forms
`r₀ r₁ … r₅` for the chain `⟨ω⟩ ⊂ ⟨ω,S₀⟩ ⊂ ⟨ω,S₀,H₀⟩ ⊂ ⟨…,S₁⟩ ⊂ ⟨…,H₁⟩ ⊂
⟨…,CZ⟩`, the last table by coset enumeration with proofs), and the Pauli
rotation lemmas of Section 4.3 (`R(P) = C_P T₀ C_P⁻¹`).  They are generated
by Python scripts kept outside the library (`Lean/Scratch/CliffordT2/py`,
not committed): the search that finds the certificates is not trusted,
only the replay in the kernel is.  The current files hold the part of the
Clifford tables found so far.

## Remaining `sorry`s

* `Equations.eqn1` … `Equations.eqn46`: the 46 equations of the authors'
  `Equation1.agda` … `Equation46.agda`, hypotheses (a) and (b) of the
  Reidemeister–Schreier theorem.  Each is an equation between two Clifford+T
  words that holds in `U(4)` (checked numerically); they are being proved by
  rewriting certificates.  A prototype shows that 40 of them reduce to the
  same Pauli-rotation normal form on both sides; Equations 21, 28, 30, 43,
  44 and 46 need, as in the paper, the "non-obvious" relations (C18)–(C20)
  (`lemma-rel-A`, `lemma-rel-B`, (C20)) at one or two places.
* Greylyn's Theorem 4.1 is used through `QCert.Greylyn.presentation`
  (folder `QCert/Greylyn/`, another formalization), whose proof is that
  folder's business.

Everything else (the Reidemeister–Schreier theorem, the five-generator
form of Greylyn's presentation with all 123 translated relations, the
translation `f`, the coset action, soundness) is proved.

## Paper errors

None found: every relation of Figure 1 holds (decided), every translated
Greylyn relation is derivable, and all 46 equations hold numerically.
