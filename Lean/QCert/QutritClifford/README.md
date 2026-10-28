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

## Completeness (Theorem 4.4): the route in progress

Not the paper's 380 box relations but a stabiliser chain, by induction on
the width `n = m + 1` (wire `0` at the bottom).  Done so far:
`Locality.lean` (`derives_pad`, `Complete`, `seg_pad`, `seg_shift`,
`negω_comm`, `negω_pow_derives`, `complete_zero`, `trivial_of_top`) and
`SchreierWords.lean` (`schreier_words`, `schreier_fix`).

**Invariant.** `Inv m := Complete m ∧ S1 m`, where `S1 m` is the stage-1
Schreier condition at width `m` (below).  `Inv (m + 1)` follows from
`Inv m` and the local facts placed on the bottom wires; a local fact on
`k ≤ 3` wires is derived once at width `k` and moved by `derives_pad`.
At width `k` itself its derivation may replace any segment on fewer wires
by `seg_pad`/`seg_shift` (completeness at width `< k` is already known).

**Stage 1** (base point `Zbot`: `Z` on wire 0, phase 0; points: the
non-scalar Paulis).  `K₁` is the submonoid generated by every generator
except `H` on wire 0, together with the word `Z` on wire 0.  Sections
(time order, `⨾`):
* top part non-scalar: `σ(y) = P_c ⨾ Γ_{a₀b₀} ⨾ top (σ'(ŷ))`, where
  `ŷ` is the top part with phase 0 and `σ'` the section one width down;
* top part scalar: `σ(y) = P_c ⨾ α_{a₀b₀}`;
* `P_c = X^{2c}` on wire 0 (`Z ↦ ω^c Z`), `α_{ab}` on wire 0 (`Z ↦ X^aZ^b`,
  `α₀₁ = 1`), `Γ_{ab}` on wires 0,1 (`Z₀ ↦ X^aZ^b ⊗ Z₁`), planned as
  `Γ_{ab} = Γ₀₁ ⨾ α_{ab}` for `(a, b) ≠ 0` and `Γ₀₀` a swap;
  `σ(Zbot) = 1`, and `σ(ω^c y) = P_c ⨾ σ(y)` by definition.
Generator cases: `-ω` (commutes); `up g'` (stage 1 one width down, then
the shifted `K₁'`-letters `S₁`, `Z₁`, `CZ₁₂` and the phase `X₁^{2δ}` pass
`Γ`); `H`, `S` on wire 0 (through `α`, then `Stab(Z)`-letters through `Γ`
and `P`); `CZ₀₁` (through `top Γ'` or `top α'` and `Γ`: the only
three-wire facts besides `CZ₁₂` through `Γ`).

**Stage 2** (inside `K₁`; base point `Xbot`; points `ω^c X Z^i ⊗ x̂`).
`K₂` is generated by the top letters and `-ω`.  Sections
`τ(x) = Q_{c,i} ⨾ CZ₀₁ ⨾ top (σ'(x̂))` (`x̂` non-scalar), `τ(x) = Q_{c,i}`
(`x̂` scalar), `Q_{c,i}` on wire 0 (`X ↦ ω^c X Z^i`, `Q₀₀ = 1`).  The case
`up g'` needs only stage 1 one width down and `K₁'`-letters commuting
with `CZ₀₁` ((C8), (C15), structural, and `Z₁`, `X₁` against `CZ`);
`CZ₀₁` needs `CZ₀₁ ⨾ top Γ' ⨾ CZ₀₁` facts on three wires.

**End.** A word `u` with trivial operator fixes both base points, so
`u ≈ k₁ ∈ K₁ ≈ k₂ ∈ K₂ ≈ top v ⨾ (-ω)^t ≈ 1` (`trivial_of_top`); then
`w ≈ v` from `u = v⁻¹ w` with explicit inverse words (powers of letters).

**Local facts** are generated by `gen/` (Python, checked numerically on
Pauli data and matrices) and checked in Lean by a rewriting engine.

## Remaining `sorry`s

| Name | Stands for |
| --- | --- |
| `complete` (`Theorem.lean`) | Theorem 4.4: Lemma 4.2 and Proposition 4.3 (every circuit rewrites to a normal form by the 380 box relations of Appendix C) and the supplement's derivation of the box relations from C1–C18; the uniqueness of normal forms it also needs is `nf_unique` |

Everything but `complete` (and what uses it: `subpresentation`,
`presentation`) has no `sorry`: soundness, generation
(`cliffordGroup_le_closure`), the normal forms (Proposition 3.9) and the
order of `𝒞ₙ` (`card_cliffordGroup`, Corollary 3.10).

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
