# CCX+H on three wires: a missing rule, and the shape of the group

The natural CCX+H rules (`../NaturalP/Syntactics.agda`) were
**incomplete on three wires**. One rule fixes that, at least as far as
the computations below can see:

    CCXH⁴ :  (CCX · H)⁴ = CZ↑        (H on the target, CZ on the controls)

This is the controlled form of (X H)⁴ = −1 on one wire: under two
controls, the −1 becomes the CZ of the controls. It is now a rule of
NaturalP (sound at every width, `../NaturalP/Soundness.agda`). Nothing
else changes: from four wires on, completeness comes from CCX+HH, and the
rule needs three wires.

The scripts here need only Python 3 (no numpy or sympy). Run them with
`python3 -B` from this directory.

## Why the old rules are incomplete

Let G₃ be the three-wire CCX+H group, Θ the CCX+HH group (W(E8), no
single H), C₃ the real Clifford group (no CCX), and A = Θ ∩ C₃. Then
`grp.py` (a small Schreier–Sims, `ss.py`) and `lat.py` give:

| Group | Order |
| --- | --- |
| Θ = W(E8) | 696729600 |
| C₃ | 5160960 |
| A = ⟨X, CX, HH⟩, the even-H Clifford circuits | 2580480, index 2 in C₃ |

Also Θ ∩ H₀ΘH₀ = A.

On three wires, every rule other than CCXH⁴ holds in Θ (it uses no
single H) or in C₃ (it uses no CCX). The schema starts at four wires.
So the rules present at most the amalgam Θ *_A C₃.

In that amalgam, `CCX H CCX H CCX H CCX H CZ↑` is a reduced
alternating word of length eight: CCX ∉ A, and H ∉ A. By the normal-form
theorem for amalgams it is not the identity, so the old rules do not
derive CCXH⁴.

## The graph of E8 lattices

G₃ acts on the lattices g·E8 (g ∈ G₃). The stabiliser of E8 is Θ.
Neighbours are E8 ~ θH₀·E8 with θ ∈ Θ, so each lattice has 270
neighbours. Call this graph Γ.

- **Distance.** The relative position of two such lattices is given by
  their elementary divisors over ℤ[√2] (π = √2; `osnf.py`), and is
  computed fast from π-adic valuations (`geo.py`). Neighbours sit at
  (−1⁴, 1⁴). The Γ-distance is the largest exponent.
- **Distance two** (`tree2.py`, `tree3.py`, `types.py`). The 36765
  vertices at distance two come in four kinds, by the number of common
  neighbours with E8:

  | Position | Common neighbours | Vertices | Group fixing the pair |
  | --- | --- | --- | --- |
  | (−2, 0⁶, 2) | 30 | 135 | W(D8) (the frames of E8); the pair is E8 and CCZ·E8 |
  | (−2², 0⁴, 2²) | 6 | 3150 | the D4 ⊕ D4 decompositions |
  | (−2³, 0², 2³) | 2 | 16200 | |
  | (−2⁴, 2⁴) | 1 | 17280 | tree-like |

  So Γ has 4-cycles and G₃ is not Θ *_A C₃. That is expected: G₃ acts
  on the building of an orthogonal group of rank 4 over ℚ₂(√2), not on
  a tree.
- **Every square comes from position (2, 0⁶).** For every pair at
  distance two, its common neighbours are connected by pairs at
  position (−2, 0⁶, 2) (`sq6.py`). So every 4-cycle is a sum of 4-cycles
  with a diagonal at that position. Those are the squares around E8 and
  CCZ·E8 = E8′, whose 30 common neighbours are θH₀·E8 with θ ∈ W(D8).
  Two such paths differ by "CCZ normalises W(D8)", and for the
  generators of W(D8) in A that is a Clifford fact. What is left is
  θ = CCX: CCX·CCZ·CCX = X·CCZ·X, which is CCXH⁴ (`r30.py` checks
  both).
- **Loops contract** (`contract.py`). Take a random loop from E8 and
  repeatedly replace its farthest vertex x, between a and b, by a common
  neighbour of a and b one step closer. Every loop tried, up to length
  26, contracts using only backtracks and squares. So, empirically, G₃
  is presented by Θ, C₃ and CCXH⁴.

## The proof in Agda (`../NaturalP/ThreeWire/`)

Completeness on three wires is Clément's translation
(`CCX+HH/Translation`, as in `../ThreeQubit/`) with a decoder of our
own. The relations to derive are every relation of Tables 1 and 2 on
eight levels, decoded (2133 instances), and the nine generators against
the decodings of their encodings. Every one is derived from the rules by
a contraction found here.

- **Theta-words.** `Kit` has θ-words: CCX+HH circuits read through θ.
  Two with one matrix are equal (`Θstep`), by completeness of CCX+HH on
  three wires. The matrices are compared by integer row actions
  (`CCX+HH/Natural/ThreeWire/Fast`), about 0.2 s per check, against 9 s
  for the dyadic matrices. `Kit` also moves H past the Clifford letters
  (`hc`).
- **CCZ.** `Letters` moves CCZ past the nine letters of W(D8) (`zc`). The
  CCX letter needs the new rule; every other letter goes through `hc`.
- **The steps** (`Steps`):
  - `CF`: the canonical form φ·CCZ·ω of a word θH θH θ at position
    (2, 0⁶).
  - `SQ`: a square, which is L30 on the two words obtained by rotating
    it.
  - `BT`: a backtrack.
  - `MG` and `TH`: Θ‑steps.
- **Chains.** A derivation is a chain of segment replacements on a list
  of θ-words and H (`Chain`, after Real-Clifford+CH's SegChain).
  `chain.py` contracts the loop of each instance, `deriv.py` and
  `geo.py` supply the geometry, and `emit_family.py` writes the chains
  (`Inst/`).
- **Dispatch.** The dispatch (`Disp/`) is by cases on the indices, with
  the impossible orders refuted.
- **Decoder.** `decoder.py` writes the decoder: X[a,b] is a W(D8)
  letter word, M[a] is k·CCZ·k⁻¹, K[s] is r·K₀·r⁻¹ with
  K₀ = H·θ₂·H·θ₃, and IH is H (`DecTable`, `Decoder`, `Elements`).
- **Assembly.** `Relations` and `Recovery` give the translated
  relations, and `Complete` concludes `complete₃`.

About 30 000 matrix checks in all. Regenerate with `gen_all.sh`
(families), `emit_relations.py`, `emit_recovery.py`,
`emit_dectable.py` and `emit_letters.py`.
