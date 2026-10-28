# Qutrit Clifford circuits

Li, Mosca, Ross, van de Wetering and Zhao, *A Complete and Natural Rule
Set for Multi-Qutrit Clifford Circuits*, QPL 2025, arXiv:2508.14670.
Formalized from the paper (TeX source and PDF), independently of the Agda
development.

## Statement

| File | Contents | Paper |
| --- | --- | --- |
| `Syntax.lean` | gates `-ω`, `H`, `S`, `CZ`; derived generators (D1)–(D11); the eighteen rules `Rule.C1`–`Rule.C18`, each on the wires it is drawn on; the theory `Theory = Lift (Padded Rule)` | §2.1, Figures 1 and 5 |
| `Semantics.lean` | `ω = e^{2πi/3}` (`ωℂ`), the gate matrices `Hmat`, `Smat`, `CZmat` as printed, `gateSem`, `sem n`; the Pauli group `pauliGroup n` and the Clifford group `cliffordGroup n` | Definitions 2.1–2.4, §2.1 |
| `Theorem.lean` | `sound`, `complete`, `subpresentation`, `presentation`, `card_cliffordGroup` | Theorem 4.4, Proposition 3.9, Corollary 3.10 |

Conventions:

* **Wires.** The paper draws the first qutrit on top; the framework numbers
  wires from the bottom (wire 0 is the bottom wire, the least significant
  digit). On `k` wires the paper's top wire is wire `k - 1`. `CX` (D7) has
  its control on wire 1 and its target on wire 0, `XC` (D8) the reverse;
  on three wires the paper's top, middle and bottom qutrits are wires 2, 1
  and 0, so `CZ₀₂` is the remote `CZ` (D9).
* **Order.** The paper writes circuits left to right in time order; words
  of the framework are in operator order. `a ⨾ b` (`QutritClifford.seq`)
  is `a` followed by `b`, i.e. `b * a`, so every rule reads left to right
  as its figure. A phase `· λ` drawn after a circuit is a scalar gate.
* **The Clifford group.** Definition 2.3 is the normaliser of the Pauli
  group; §2.1 restricts it to matrices with entries in `ℤ[1/3, ω]`, the
  group whose order Corollary 3.10 gives. `cliffordGroup n` is that group.
  `presentation` states that the rules present it, with each generator
  read as its matrix; `subpresentation` states the same for the group the
  generators generate inside `U(3ⁿ)`.

## Proved

* `Soundness.lean`: every rule holds at every width (`rule_sound`,
  `theory_sound`, `sound`), and every generator has an inverse modulo the
  rules (`grouplike`: `(-ω)⁵`, `H³`, `S²`, `CZ²`). The rules are decided
  over `ℚ(ζ₁₂)` (`Quartic 1 (-1)`, carried to `ℂ` by `toC`) by
  `decide +kernel`.
* `Trie.lean`: the evaluator behind those decisions. A vector on `n`
  qutrits is a trie of nested triples; a gate acts on it by recursion on
  the wires (`Vec.act`, with `get_act : get (act g v) = gen g *ᵥ get v`),
  and two circuits have the same operator when they send every basis
  vector to the same trie (`Vec.eval_eq_of_cols`). Evaluating the
  framework's matrices directly makes the kernel recompute every entry of
  every intermediate product, which did not finish for two-qutrit rules.
  To keep the evaluations short, the derived gates `S'`, `SWAP`, `CX`, `XC`
  are evaluated once on their own wires (`eval_S'`, `eval_SWAP`, …) and the
  rules are decided over an extended gate set (`XGate`, `Sim`).
* `Semantics.lean`: unitarity of the gate matrices; `cliffordGroup n` is a
  subgroup (closure under inverses: conjugation by a unitary permutes the
  finite set `𝒫ₙ`).
* `Theorem.lean`: `subpresentation` and `presentation` from the lemmas
  below; general lemmas `evalShift`, `evalPad`, `genPad` (evaluation of
  shifted and padded circuits for `GateOps`) are in `Soundness.lean`.

* `Pauli.lean`: every generator's operator lies in `𝒞ₙ` (`gen_mem`, used by
  `gen_mem_cliffordGroup`): a Pauli operator on `n + k` wires is one on the
  bottom `k` wires times one on the top `n` (`pauli_split`,
  `onBottom_pauli_mul`), so a gate on the bottom wires or a generator moved
  up normalises `𝒫` when it does on its own wires (`Normalises.onBottom`,
  `Normalises.onTop`); `H` and `S` are unitary and send `X` and `Z` to
  Paulis (`H X H† = Z`, `H Z H† = X²`, `S X S† = X Z²`, `S Z S† = Z`,
  decided over `ℚ(ζ)` on `3 × 3` matrices), and conjugation is
  multiplicative, so the one-qutrit Pauli calculus (`pauliQ1_mul`, from
  `Z X = ω X Z`) gives the rest; `CZ`, diagonal, by the exponent identity
  of its action (`cz_exponent`, decided on `Fin 3`); the entries of `H` lie
  in `ℤ[1/3, ω]` since `(ω² - ω)⁻¹ = (ω - ω²)/3`.
* `Phases.lean`: Proposition 2.8 (`scalar_of_fixes`: a unitary fixing every
  Pauli by conjugation is a scalar; the paper argues that the Paulis span
  all matrices, here the `Z`-type Paulis make it diagonal and the `X`-type
  ones make the diagonal constant), Lemma B.1 (`three_dvd_of_nine_dvd`,
  decided mod 9), Proposition B.2 (`phase_of_mem`: the elements of
  `ℤ[1/3, ω]` of norm one are the powers of `-ω`; `mem_ZThirdOmega` writes
  an element as `(a + bω)/3ᵏ`) and Corollary B.3 (`same_action_phase`: two
  elements of `𝒞ₙ` acting alike on `𝒫ₙ` differ by a power of `-ω`). With
  them `cliffordGroup_le_closure` (generation) follows from the existence
  half of Proposition 3.9.
* `PauliAction.lean`: Pauli data `PD n` (phase, `X` and `Z` exponents per
  wire), their multiplication law (`PD.op_mul`), injectivity of the
  operator (`PD.op_inj`), and the action of circuits on Pauli data as an
  explicit, computable function `actC` with `sem_conj`:
  `sem w · P · sem w† = actC w P`. Facts about the action of a fixed
  circuit on Paulis are then decided by computation on the data.
* `NormalForm.lean`: the boxes `A`–`F` of Figure 9 and both columns of
  Figure 8 (their required and additional actions), decided on Pauli data
  for every index; the `Z`- and `X`-normal circuits of Figure 10 as data
  (`ZN`, `XN`) together with the Pauli each sends to `Z` on the top wire,
  resp. `X` on the bottom wire, which determines it: Lemmas 3.5–3.7.
* `Prop39.lean`: Lemma 3.8; Proposition 3.9, existence (`exists_nf`: every
  unitary normalising `𝒫ₙ` acts on it as the layers of a normal form do —
  an operator fixing `Z` and `X` on the bottom wire acts on the other wires,
  `eq_onTop`, and normalises their Paulis, `normal_of_onTop`) and
  uniqueness (`nfx_unique`, and `nf_unique` with the phase `(-ω)^t`).
* `Count.lean`: normal forms are in bijection with `𝒞ₙ` (`nfEquiv`), and
  Corollary 3.10 (`card_cliffordGroup_eq`), so `exists_circuit_action` and
  `card_cliffordGroup` are proved.

## Completeness (Theorem 4.4)

`complete` is `complete_all` (`Stage2.lean`).  Not the paper's route (the
380 box relations of Appendix C, derived from C1–C18 in its supplement) but
a stabiliser chain, by induction on the width.

**Up to a phase, on words of letters.**  Derivations are carried out up to
a power of `-ω` (`PEq`, `Proj.lean`): the scalar commutes with every
circuit and its powers are determined by their value, so the phase is
recovered at the end (`der_of_peq`; `negω_comm`, `negω_pow_derives` and
`derives_pad`, a derivation on `k` wires holding on the bottom `k` of more,
are in `Locality.lean`).  Every circuit is, up to a phase, a
word of letters (`H`, `S` on a wire, `CZ` on two adjacent wires, in time
order; `exists_word`), so completeness on `n` wires follows once every
word acting trivially on the Pauli operators is derivably trivial
(`complete_of_words`, `Words.lean`).  With completeness on fewer wires, a
segment of a word on a proper block of adjacent wires may be replaced by
any segment acting alike on the Paulis there (`pcomplete`, `Proj.lean`).

**The engine** (`Run.lean`, `Engine.lean`, `Local.lean`).  A derivation
on two or three wires is a run of steps over a table of equations: a rule
step replaces an occurrence (up to commuting letters on disjoint wires,
`canon`) of one side of an entry by the other; a free step replaces a
segment on the bottom or top `k - 1` wires by one with the same Pauli
action, sound given completeness on `k - 1` wires (`fo2_sound`,
`fo3_sound`).  Libraries of lemmas, each over the table before it, are
stored as numbers and decided lemma by lemma by `decide +kernel`
(`libLemOk`, `validUpTo_all`).

| Width | Proof | Modules |
| --- | --- | --- |
| 0 | by (C1) | `Locality.lean`: `complete_zero` |
| 1 | a coset certificate: the 216 elements of the projective one-qutrit Clifford group, the table of the action of `H` and `S`, and every entry deduced from (C2)–(C5) by scanning one relator around the table, all its other entries coming earlier (`Cert.edges`); a word acting trivially reaches the coset of the empty word | `Coset.lean`, `CosetCheck.lean`, `Cert1Data.lean`, `Cert1.lean`: `complete_one` |
| 2 | a coset certificate: the 90 cosets of the local subgroup (one-wire gates on each wire), entries deduced from (C2)–(C14), the commutation of one-wire gates on different wires and 15 stabiliser facts of the two-wire library (105 lemmas from (C6)–(C14) with free one-wire segments, `Lib2*.lean`); a word acting trivially is a local word times the representative of its coset, no representative but the first acts like a local word (`cert2_reps`), and a local word acting trivially is trivial by completeness on one wire (`local_trivial`) | `Cert2Data.lean`, `Cert2.lean`: `complete_two` |
| `n + 1 ≥ 3` | the two Schreier stages below, from completeness on `n` wires and the stage-1 condition there | `Points.lean`, `Sections.lean`, `Facts.lean`, `Stage1.lean`, `Stage2.lean` |

**Points and sections** (`Points.lean`, `Sections.lean`).  A Pauli
operator up to a phase is a list of exponent pairs, wire `0` first, on
which letters act by conjugation (`ptAct`, `ptRun`); this is the action of
the circuits on Pauli data (`toPt_run`).  Sections, in time order:
`alpha p` on wire `0` sends `Z` to `p`; `Gam p` on wires `0, 1` sends `Z₀`
to `p ⊗ Z` (`H³ ⨾ CZ ⨾ H ⨾ alpha p`, and the swap for `p = 1`); the
stage-1 section `sigma y` sends `Z₀` to `y` (`alpha` of its wire-`0`
factor if the rest is trivial, otherwise `Gam` of it followed by the
section of the rest one wire up); the stage-2 section `tau ((1, i) :: y)`
is `S^{2i}` on wire `0`, then, unless `y` is trivial, `CZ` and `sigma y`
one wire up: it sends `X₀` to the point and fixes `Z₀`.

**Stage 1** (`Stage1.lean`).  The condition `S1 n`: for every letter `x`
and point `y ≠ 1`, `sigma y ⨾ x = k ⨾ sigma (x·y)` up to a phase with `k` a
word of tokens of the stabiliser of `Z₀` (`S`, `X`, `Z`, `CZ` at the
bottom and the letters above wire `0`).  On two wires it holds by
completeness there, with the K-words of `S12Data.lean` checked on Pauli
tableaux (`s1_two`).  On `n + 1 ≥ 3` wires (`s1_succ`): a letter above
wire `0` acts on the rest by `S1 n` one wire up, and the K-word it leaves
passes `Gam` (`gam_pass`); `H`, `S` on wire `0` pass `alpha` or `Gam`;
the swap of wires `0, 1` is treated as a whole, and `CZ₀₁` is
`W1 ⨾ W0 ⨾ CZ₁₂ ⨾ W0 ⨾ W1` (S1h).

**Stage 2** (`Stage2.lean`).  On the words of tokens of the stabiliser of
`Z₀`, acting on the points `(1, i) :: y` that `X₀` reaches: for every
token, `tau q ⨾ t = k ⨾ tau (t·q)` with `k` a word of tokens of the
stabiliser of `Z₀` and `X₀` (`X`, `Z` at the bottom, letters above wire
`0`), from `S1 n` and the local facts (`good2_tok`).

**The end** (`words_trivial_succ`).  A word acting trivially is, by stage
1, derivably a word of stage-1 tokens; by stage 2 a word of stage-2 tokens;
that is a word on wire `0` followed by a word above it (`split_K2`), and
each acts trivially on its own wires, so both are trivial by completeness
on one and on `n` wires (`k2_trivial`).  `complete_s1` runs the induction
from two wires.

**The local facts** (`Facts.lean`).  The two stages reduce to 311
equations on at most three wires in fifteen families (S1a)–(S1h),
(S2a)–(S2g), listed in the module, each of the form `lhs = k ⨾ rhs`.  They
are the main lemmas of the three-wire library (`Lib3*.lean`, 363 lemmas:
the lemmas of `gen/lib3.py`, among them (C18) turned round, the Steinberg
relation `x a = a x r` and the swaps passing the staircases, and the facts
of `gen/facts3.py`), derived by the engine from (C15)–(C18) with free
two-wire segments, so given completeness on two wires (`lib3_valid`).
Each family is matched against the table by computation (`ok_S1a`, …),
which also pins its K-words (`Facts3Data.lean`) and the Lean definitions
of the gadgets to those of the generator.

`SchreierWords.lean` (Schreier's lemma on words modulo a relation) is a
general form of the inductions of the two stages; the final proof does not
use it.

**Build times** (from scratch, with Mathlib): the three-wire library takes
about 1 min 50 s in all (31 chunks of 12 lemmas, 2–5 s each), `Facts`
15 s, `Cert1` 16 s, `Cert2` 11 s, `Stage1` 19 s, `Stage2` 11 s; the
slowest module of the folder remains `Soundness` (about 210 s).

## Remaining `sorry`s

None: `complete`, `subpresentation` and `presentation` have no `sorry`;
`#print axioms QCert.QutritClifford.presentation` gives `propext`,
`Classical.choice`, `Quot.sound`.

## Errors in the paper

* **(D6) is `-SWAP`, not `SWAP`.** The circuit `(H ⊗ H) CZ (H ⊗ H) CZ
  (H ⊗ H) CZ` of Figure 5 sends `|x, y⟩` to `-|y, x⟩`: its matrix entry
  at row `|1, 0⟩` (index 3), column `|0, 1⟩` (index 1) is `-1`. With the
  paper's `H = (ω² - ω)⁻¹ [ω^{jk}]` the six Hadamards contribute
  `(ω² - ω)⁻⁶ · 3³ = -1`. (The odd-prime paper, arXiv:2609.40106, puts the
  phase `λ_p² = -1` (for `p = 3`) into its (T4) for this reason.) The rules
  of Figure 1 use the circuit, each with the same parity of swaps on both
  sides, and all eighteen hold as printed; `swapX` in `Soundness.lean` is
  the circuit's matrix. Nothing is changed in the statement.
