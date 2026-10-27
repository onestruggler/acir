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
* `Calc.lean` — the circuits modulo the theory as a group `Q d lv n`
  (`mk` the class of a circuit), structural commutations, the central
  scalar.
* `Powers.lean` — powers labelled by `𝔽_d` of an element of order dividing
  `d`.
* `Affine.lean` — Figure 1 as group equations on the bottom wires, Lemmas
  17, 18, 19 and 21 (`X` on the target of `CX`; derived here by conjugating
  (6) with `M_{-1}` on the control rather than by the paper's chain).
* `Translation.lean` — Lemma 3, first step: an affine circuit is its
  translation column `NF_tr(b)` (`xcol`) after its linear part
  (`affine_collect`).
* `Embed.lean` — `Aff_d` inside every level: its gates and rules are those
  of every level, so its derivations lift (`derivable_lift`) with the same
  pairs (`sem_lift`), and every linear circuit comes from `Aff_d`.
* `LinearLocal.lean` — the local relations the linear normal form uses, as
  group equations on two and three wires: the multipliers against `CX`
  ((4), (5)), the Bruhat relation `s a s = a s a⁻¹ M₁(-1)` from (7)
  (`swap_conj_cx`, `bruhat`), the Yang–Baxter equation and the naturality of
  the crossing for `CX`, rule (8) as `b a L = a b` (`steinberg`), Lemmas 23
  and 24 (`lemma23`, `lemma24`), the Steinberg relation with labels, and the
  exchange of the lower entries of a stair (`stair_swap`).
* `LinearNF.lean` — the normal form of a linear circuit on `n + 1` wires: a
  *stair* `S(v)` (a linear circuit sending `e₀` to `v`, one representative
  of each coset of the stabiliser `H` of `e₀`), a *fan* `F(c)`
  (`x₀ ↦ x₀ + c · (x₁, …, x_n)`) and a linear circuit one wire up
  (`decompose`). The design is written out at the head of the module: fans
  add (`fan_add`), a linear circuit one wire up passes a fan (`passes_word`),
  and the table (`table`) rewrites a generator applied to a stair as a stair
  followed by an element of `H`.
* `Linear.lean` — completeness of the linear fragment of `Aff_d`
  (`linear_complete0`): the map of `S(v) F(c) ↑B` determines `v`, `B` (by
  induction on the number of wires) and `c`. The relabellings are computed
  through the affine map of each generator (`gen_f`).
* `AffineComplete.lean` — Lemma 2 (the column is fixed by the image of `0`)
  and Theorem 1 (`affine_complete`, at every level) from the completeness of
  the linear fragment of `Aff_d` (`linear_complete0`), lifted to every level
  (`linear_complete`).
* `LinPhase.lean` — Theorem 2 for `LinPhase_d` (`complete1`): Lemma 12
  (`zcol_push`: a diagonal normal form `ω^k Z^{a_0} ⋯ Z^{a_{n-1}}` moves
  through an affine gate by (21), (22), (23), the crossing, and `Z` on the
  control of `CX`, derived by conjugating (21) with `M_{-1}`), Lemma 15
  (`layered1`), Lemma 7 and Proposition 1 (the coefficients read off the
  phase at `0` and at the unit vectors).
* `Atom.lean` — phase atoms: a phase gate `G` on wire `0` conjugated by a
  linear circuit `W`, `W⁻¹ G W`, depends only on the first coordinate of
  `W x` (`atom_wd`). A linear circuit fixing that coordinate commutes with
  `G` (`commute_of_row0`, from the linear normal form, (7), and `G` on the
  control of `CX`: (29), (39), or the `Z` analogue). This replaces the
  placements by symmetries of Lemmas 11 and 12.
* `Rows.lean` — linear circuits act linearly (`sem_add`, `sem_smul`,
  `sem_row`); explicit linear circuits computing a given linear form
  (`rowW`) or two independent forms (`row2W`).
* `QuadAtoms.lean` — the atoms of `S` and `Z` on linear forms (`atomL`):
  placed by any circuit (`atom_eq_atomL`), commuting (`atomL_commute`;
  Lemma 11), (27) and (22) on a form (`atomL_S_smul`, `atomL_Z_smul`), `Z`
  additive by (21) (`atomL_Z_add`), and rule (28) for two independent forms
  with `CZ` written out by Definition 16 (`par_raw`).
* `JvN.lean` — the theorem of Jordan and von Neumann: a map satisfying the
  parallelogram law has a biadditive polar form (also in a group, for
  commuting values of odd order).
* `QuadDiag.lean` — the diagonal group of `QuadPhase_d` (generated by the
  scalar and the atoms of `S` and `Z`): abelian, of exponent `d`; the
  parallelogram law for `Q u = S(u)² Z(u)` (`qfun_par`), hence the `CZ` fan
  `K c` as its polar form (`kfan`, additive); every element is
  `↑D' Z₀^a Q(e₀)^b K c` (`dg_nf`; Lemma 13), with phase
  `q'(x') + a x₀ + b x₀² + 2 x₀ (c · x')`, so the pair determines it
  (`dg_inj`; Proposition 1).
* `QuadComplete.lean` — Lemmas 12, 14, 15 for `QuadPhase_d` (an affine gate
  conjugates the diagonal group into itself: linear gates by `atom_wd`, `X`
  by (23) and (25); `layered2`) and Theorem 2 for the pairs (`complete2`).
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

Proved: soundness of every rule at every level (Lemmas 1, 8, 9; no
hypotheses beyond the paper's: `2` invertible at level 2, `2, 3` at level 3),
soundness of the theories for the matrices and the pairs, grouplikeness,
the reduction of matrix completeness to completeness for pairs (Remark 2),
**Theorem 1** (`theorem1`, `theorem1ℂ`: `Aff_d` presents the affine
operators), and **Theorem 2 for `LinPhase_d`** (`theorem2_lin`,
`theorem2_linℂ`), and **Theorem 2 for `QuadPhase_d`**, `d` odd
(`theorem2_quad`, `theorem2_quadℂ`). These depend on no `sorry`. The step of
Lemma 3 that the paper takes from Lafont's linear normal form theorem [17]
is proved here directly (`LinearNF`, `Linear`), from the rules of Figure 1.

Remaining `sorry`:

* `Completeness.complete_cube` — Theorem 2 for `CubicPhase_d`, `d > 3`
  (Lemmas 10–15 and Proposition 1 for the cubic diagonal normal form, with
  the cubic certificates of Tables 4 and 5, Appendix D). The atoms of `T`
  are placed and commute by the same argument as those of `S` (`Atom`, with
  (39)); what remains is the cubic analogue of `QuadDiag`: the relations
  among atoms of `T`, `S`, `Z` from (32), (35)–(38), (40)–(42) and
  Definitions 17, 18, and the normal form they give.

## Notes on the paper

* No error found: every rule of Figures 1, 3, 4, 5, with the definitions of
  `CZ`, `CS`, `CCZ` (Definitions 16–18), is sound as transcribed for the
  interpretation of Definition 20 (Lemma 8 holds as stated).
* Rule (7) uses upside-down `CX^{-1}`; in the PROP these are the conjugates
  of `CX^{-1}` by the crossing, transcribed as `flip (CX ^ᶠ (-1))`.
* Some derivations differ from the paper's: Lemma 21 (`X` on the target of
  `CX` commutes with it) and `Z` on the control of `CX` commuting with it
  (used for the transport of Lemma 12) are both obtained by conjugating a
  rule ((6), resp. (21)) with `M_{-1}` on the control, which inverts `CX`
  ((4)) and `X` (Lemma 18), resp. `Z` ((22)). Lemmas 23 and 24 (`CX` from
  the middle wire, resp. from the top wire to the middle wire, commutes with
  `CX` from the top wire to the bottom wire) follow from (8), read as
  `L = a⁻¹ b⁻¹ a b`, and its conjugates by `M_{-1}` on the bottom wire
  (inverting `a` and `L`) and on the top wire (inverting `b` and `L`); the
  argument is uniform in `d`, including `d = 2`.
* The quadratic diagonal calculus here does not follow Tables 3 and 4: all
  placements come from `atom_wd`, and the bilinearity of `CZ` from the
  parallelogram law (28) by the theorem of Jordan and von Neumann. Rule (30)
  is not used in the proof of completeness of `QuadPhase_d`; since it is
  sound, it is derivable from the other rules of `QuadPhase_d`.
* The paper does not prove the completeness of its linear fragment; it cites
  Lafont [17] after deriving Lafont's rules (Lemma 16). The normal form used
  here instead (stairs and fans, `LinearNF`) needs only (2), (4), (5), (7),
  (8) and the symmetry rules.
