# Prime-dimensional phase-affine circuits (Blake 2026)

C. Blake, *Completeness for Prime-Dimensional Phase-Affine Circuits*,
arXiv:2603.06466 (QCert Table 1: "phase-affine, prime d — sub-presentations").
Formalized from the paper alone.

For a prime `d` (`[Fact d.Prime]`, labels in `ZMod d`), four nested
fragments, indexed by a level `lv`:

| level | fragment | gates | rules | side condition |
|---|---|---|---|---|
| 0 | `Aff_d` | `X`, `M_a` (`a ∈ 𝔽_d^×`), `CX`, `SWAP` | (1)–(8), Figure 1 | — |
| 1 | `LinPhase_d` | + `ω`, `Z` | + (19)–(23), Figure 3 | — |
| 2 | `QuadPhase_d` | + `S` | + (24)–(30), Figure 4 | `d` odd |
| 3 | `CubicPhase_d` | + `T` | + (31)–(42), Figure 5 | `d > 3` |

## Files

* `Syntax.lean` — the gates (`Gate d lv k`, a phase gate carrying its level
  evidence), the derived diagonals `CZ`, `CS`, `SC`, `CCZ` (Definitions 16,
  17, 18, transcribed gate by gate), and the rules `Rules d lv`, one
  constructor per equation of Figures 1, 3, 4, 5 (`r1` … `r42`, the
  paper's equation numbers) on the wires it is drawn on, plus the symmetry
  of the PROP (`swap_inv`, `swap_nat1`, `swap_nat2`). `theory d lv` is
  `Lift (Padded (Rules d lv))`.
* `PhAff.lean` — the semantic operators `P_g D_q` of Section 3.3 as pairs
  `PA d n` (relabelling `f`, phase function `q`), their composition
  (Definition 13), restriction to wires, and the matrices `toOp ψ`: the
  entry in row `|s⟩`, column `|t⟩` is `ψ (q t)` if `s = g t`, else `0`.
  `toOp_injective`: with an injective character the matrix determines the
  pair (Remark 2).
* `Semantics.lean` — the pair of each gate (Definitions 6 and 20:
  `X ↦ P_{x+1}`, `M_a ↦ P_{ax}`, `CX ↦ P_{(x,y) ↦ (x, x+y)}`,
  `SWAP ↦ P_{(x,y) ↦ (y,x)}`, `ω ↦ ω`, `Z ↦ D_x`, `S ↦ D_{binom x 2}`,
  `T ↦ D_{binom x 3}`) and the matrix semantics `sem lv ψ hψ : GateSem`.
* `Soundness.lean` — Lemma 8 (`sem_CZ`, `sem_CS`, `sem_CCZ`: the exponents
  `xy`, `x binom y 2`, `xyz`), Lemmas 1 and 9 (`rules_sound`: every rule,
  symbolically in `d`), `theory_sound` (matrices), `pa_sound` (pairs).
* `Derive.lean` — general tools: a derivation moved up a wire, a rule on the
  bottom wires.
* `Grouplike.lean` — every generator is invertible in the theory.
* `Completeness.lean` — completeness for the pairs, one theorem per level.
* `Theorem.lean` — the four main theorems `theorem1`, `theorem2_lin`,
  `theorem2_quad`, `theorem2_cube` as
  `IsSubPresentationOf (theory d lv n) ((sem lv ψ hψ).gen (n := n))`, and
  their instances over `ℂ` (`theorem1ℂ`, …).

## Conventions

* **Wires.** Wire `0` is the bottom wire of a diagram. The paper's `CX` has
  its control on the top wire: here `CX` has control wire `1`, target wire
  `0`, `(x, y) ↦ (x, x + y)` with `x` on wire `1`. On three wires the
  paper's top, middle, bottom wires are `2, 1, 0`; on four (rule (41)) the
  wires `3, 2, 1, 0`.
* **Order.** Words are in operator order (`w * v` applies `v` first). Rules
  are written with `seq [g₁, …, gₖ]`, which applies `g₁` first, so that
  they read left to right as drawn. Gates drawn in one column on disjoint
  wires are listed top to bottom.
* **Labels.** A gate labelled by `k ∈ 𝔽_d` (`X^x`, `CX^{-x}`, `S^{x²}`,
  `Z^{binom x 2}`, …) is the `k.val`-fold iterate `w ^ᶠ k`, which for the
  label `-k` is the `(d - k)`-fold iterate, the paper's convention for
  negative labels. `binom2 x = x (x-1) 2⁻¹`, `binom3 x = x (x-1) (x-2) 6⁻¹`
  in `𝔽_d`.
* **PROP structure.** The framework has no built-in symmetry. `SWAP` is a
  two-wire gate of every level, and the laws of the symmetric structure are
  rules: `swap_inv` (`σ σ = id`), `swap_nat1` (naturality for every
  one-wire gate) and `swap_nat2` (naturality for every two-wire gate,
  `σ_{2,1} = cyc`; at the gate `SWAP` it is the Yang–Baxter equation).
  With the framework's structural rules (shift, interchange, scalars) they
  present the free PROP on the generators. A gate drawn upside down or on
  non-adjacent wires is the placed instance conjugated by crossings:
  `flip w = SWAP w SWAP`, `long w` (top wire of `w` on wire `2`, bottom on
  wire `0`, conjugated by the crossing of the wires `1, 2`), `long3 w` (top
  wire of a three-wire `w` on wire `3`).
* **Semantics.** Over any commutative ring `A` with an involution and an
  additive character `ψ : 𝔽_d → A` with `star (ψ a) = ψ (-a)`, `ψ a`
  standing for `ω^a`; completeness assumes `ψ` injective (`ω` primitive).
  `semℂ` is the paper's `ℂ` with `ω = e^{2πi/d}` (`ZMod.stdAddChar`).

## Status

Proved: soundness of every rule at every level (no hypotheses beyond the
paper's: `2` invertible at level 2, `2, 3` at level 3), soundness of the
theories for the matrices and the pairs, grouplikeness, and the reduction of
matrix completeness to completeness for pairs.

Remaining `sorry`s (`Completeness.lean`):

* `complete_lin0` — Theorem 1 (with Lemmas 2, 3: the affine normal form).
* `complete_lin1`, `complete_quad`, `complete_cube` — Theorem 2 (Lemmas
  10–15, Proposition 1) for the three phase fragments.

## Notes on the paper

* Rule (7) uses upside-down `CX^{-1}`; in the PROP these are the conjugates
  of `CX^{-1}` by the crossing, transcribed as `flip (CX ^ᶠ (-1))`.
* The paper's rule figures and its interpretation (Definition 20, Lemma 8)
  agree: every displayed equation was found sound as transcribed.
