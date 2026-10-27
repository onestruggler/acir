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

## Remaining `sorry`s

| Name | Stands for |
| --- | --- |
| `complete` (`Theorem.lean`) | Theorem 4.4: Proposition 3.9 (unique normal forms, Lemmas 3.5–3.8), Lemma 4.2 and Proposition 4.3 (normalisation by the 380 box relations of Appendix C), and the supplement's derivation of the box relations from C1–C18 |
| `gen_mem_cliffordGroup` (`Theorem.lean`) | each generator normalises the Pauli group and has entries in `ℤ[1/3, ω]` (Appendix D, generator actions) |
| `cliffordGroup_le_closure` (`Theorem.lean`) | Proposition 3.9 (existence of normal forms: every Pauli automorphism is a circuit) and Corollary B.3 (the phases of `𝒞ₙ` are the powers of `-ω`) |
| `card_cliffordGroup` (`Theorem.lean`) | Corollary 3.10 (counting normal forms) |

`sound`, `grouplike`, `rule_sound` and everything in `Soundness.lean`,
`Trie.lean` and `Semantics.lean` have no `sorry`.

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
