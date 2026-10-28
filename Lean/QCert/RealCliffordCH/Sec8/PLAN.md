# Lemmas 8.7 and 8.8: plan and work packages

Targets: `Sec8.lemma_8_7` (`Lemma87Proof.lean`) and `Sec8.lemma_8_8`
(`Lemma88Proof.lean`), at width `n ≥ 3`, with completeness on fewer wires
as hypothesis.  The paper's proofs are Appendix E (Lemmas 8.4–8.6, the
decoding of each rule of Figure 8), resting on the auxiliary equations of
Appendix D: about 1,850 derivation steps in all (D.2: 189, D.3: 628,
D.4: 144, D.5–D.9: 692, E: 202, counted as `=` signs in the PDF text).

## The simplification

At width `n` we hold `IH n := ∀ k < n, CompleteAt k` (`Weak.lean`).  So every
citation of an equation on fewer wires — `(XX)ₙ₋₁`, `(XX)ₙ₋₂`, "Lemma D.3",
"Lemma D.6", "Lemma 7.6", "Lemma 5.1", and every fixed-width equation of
D.1–D.4 used at a larger width — is one **semantic step**: a window of the
circuit that is idle on some wire is replaced by any window with the same
semantics, idle on the same wire.  Only citations at the current width
`(XX)ₙ` need real derivations.  Each schema is proved directly at width `N`
(no induction on `N` in Lean: the paper's induction is the hypothesis).

The semantic step (`Weak.lean`):

* `sem_step_shift`, `sem_step_top`, `sem_step_pad`: windows `shift a`
  (idle on wire 0), `padTop a` (idle on the top wire), `pad m a` (on the
  bottom `k < N` wires);
* `window`: a window `w` that an invertible `c` (`c * c' ≈ 1`, typically a
  swap network and its reverse) conjugates to `shift a` may be replaced by
  any `v` with the same semantics that `c` conjugates to some `shift b`;
* `window'`: the same with the semantic hypothesis one wire down
  (`S.sem N a = S.sem N b`), which is usually the cheaper one to decide;
* `small_of`: a fixed-width equation on `K` wires holds on the bottom of
  `m + K` wires: semantically for `m ≥ 1`, by its own derivation for `m = 0`.

`WeakTest.lean` exercises `window`/`window'` on windows conjugated by the
swap of wires 0, 1 (three wires) and by the two-swap network carrying wire
2 down to wire 0 (four wires).

**Performance of semantic checks.**  `Sim.check` under `decide +kernel` is
slow beyond three wires: about 3 minutes for a 40-gate comparison on three
wires, and more than 6 minutes (not finished) for 80 gates on four (each
swap is 9 gates, 6 of them `H`).  Decide the semantics of a window one wire
down (`window'`) whenever possible, and package (i) should give the engine
a faster checker before D.3/D.4: swaps as permutations of basis states, `Z`
and `CZ` as signs, and the `H` gates over `ℤ[√2]` with a global power of
`1/√2` instead of rationals.

To use `window`, bring the window to `shift` form by swap-network
naturality: conjugating a gate on small wires by a small network is itself a
small-width equation, hence free when the width allows; for networks that
span all wires (`down t`, `netL`) prove the naturality once, from
(f1)–(f4), (g) and the structural rules.

## Conventions (`MC.lean`, `Syntax.lean`, `Decoding.lean`)

* Wire 0 is the bottom wire (least significant bit).  Circuits are written
  with `drawn [g₁, g₂, …]` in the order of the figure (`g₁` applied first).
* Canonical multi-controlled gates (Definition 2.4, `Syntax.lean`), `k`
  controls: `box k : Circ (k+1)` (box wire 0, controls `1…k`), `zx k`,
  `xz k : Circ (k+1)` (target 0), `mch k : Circ (k+2)` (box wire 0, `H`
  on wire 1, controls `2…k+1`).
* `atBot N g`: `g` on the bottom wires, idle wires above (`padTop`).
* `netL N ps`: brings the wires `ps = [p₀, p₁, …]` down to `0, 1, …`, one
  at a time (`moveDown`), the other wires keeping their order.
  `placeG N g ps` = network, `g`, network reversed: `g`'s wire `i` on
  wire `ps[i]`.  Definition 8.3's `placeAt` / `placeAt2` are the instances
  `ps = t :: …` / `ps = b :: h :: …` (same swap lists).
* Colours: `colourW N ws g` = `X` on the wires `ws` on both sides (Figure 3);
  `(81)` is `D.eq81`.
* **`mc N K tg c`** — the general multi-controlled gate.  `K ∈ {box, zx,
  xz, hg}`; `tg` = `[box wire]`, `[target]`, or `[box wire, H wire]`;
  `c : ℕ → Option Bool` the controls (`some true` black, `some false`
  white, `none` idle).  Built as `colourW` of `placeG` of the canonical gate
  on `tg ++ (control wires increasing)`.  Helpers: `blackOn lo hi`,
  `colOn lo hi x` (the paper's `Λˣ` on the wires `lo…hi-1`), `ctlAt j b`
  (a single control; the half-black dots of Lemma D.13 are Boolean
  parameters), `ctlOr`, `setCtl`, `DiffOn` (`x ≠ y` on a block),
  `Kind.sgnZX a` (`(-1)ᵃ ZX`: `zx` or `xz`).  Small gates: `zAt`, `hAt`,
  `czAt`, `chAt` (`H` wire, control wire), `ppAt`, `xAt`, `swAt`.
* The Python model `r87/mc.py` (scratch) mirrors these definitions gate
  for gate (checked equal to the Lean definitions on examples) and
  `mc` was checked against its intended semantics (`Λ_c(U)`) on 500 random
  placements, colourings and kinds at widths 2–6.

## Dependency order at width `N` (same-width citations only)

`269 (def) → 272 (19ₙ) → 271, 273, 274, 286, 287 → 275 → 276 → 277 → 278 →
279 → 280 → 282 → 283 → 284 → 285 → 288–295 → 296 → 297 → 298 → 299 →
300 → 301 → 302 → 305, 306 → 307; 308 (induction on C: 274, 19, 285, 272,
280); 309–313; 314; 315–328; 335–340, 342, 344, 345; 333, 334; 346–352;
353, 354; 355–360; E: 8.4, 8.5, 8.6 ⇒ lemma_8_7; E.5 (361 inside rule
(43)) ⇒ lemma_8_8.`

Not needed by E (transitively): 270, 281, 303, 304, 329–332, 341, 343.

Proofs of D.12/D.13 are inductions on the number of controls: in our
setting the induction hypothesis is a semantic step one width down.

## Fixed-width equations (Appendices D.1–D.4)

Cited by the chain at full width only when `N` equals their width:
D.2 (3 qubits) at `n = 3`, D.3 (4 qubits) at `n = 4`, D.4 (5 qubits) at
`n = 5`; for `n ≥ 6` all are free.  At `n = 3` the boxes are `CZ`s
(`box 2 = shift cz`), so `n = 3` is light.  Cited by D.5–D.9 and E:
117, 118, 124–132, 136–148 (D.2); 157, 160, 168, 172–174, 209, 214–218,
221–226, 232–235, 238, 240–248 (D.3); 267, 268 (D.4); plus their own
dependencies inside D.2–D.4.  The figures are vector graphics (wires,
filled/white dots, labelled boxes, dashed boxes, swap curves): a PyMuPDF
parser transcribes them; each transcribed line is checked numerically and
against the equation numbers cited under it, and any failing line is
re-rendered at high resolution before the paper is suspected.

Interface form (file `D/Small.lean`, to be created by the parser): the
circuits `lNNN rNNN : Circ K` and

    theorem eqNNN (m : ℕ) (ih : IH (m + K)) :
        Derivable (theory (m + K)) (Circuit.pad m lNNN) (Circuit.pad m rNNN)

proved by `small_of` (semantic for `m ≥ 1`, decided by `Sim.check`) from
the width-`K` derivation, which is the package's work.

## Work packages

Each package owns its files and proves the statements it exports without
editing the others; it may assume everything exported by the others (the
`sorry`s are listed in the README).

* **(i) D.2 and `n = 3`** — `D/W3*.lean`: the 3-qubit equations (117)–(147)
  at width 3 from Figure 4 and two-qubit completeness, via a concrete-width
  rewriting engine (letters = placed gates; steps = table rewrites up to
  commutation of disjoint gates, and `shift`/`padTop` window steps decided
  by `Sim.check`).  Exports the `m = 0` cases of `eqNNN` for D.2.
* **(ii) D.3 and `n = 4`** — `D/W4*.lean`: (150)–(248) at width 4 from
  completeness on three qubits.  Exports the `m = 0` cases for D.3.
* **(iii) D.4 and `n = 5`** — `D/W5*.lean`: (249)–(268).  Exports the
  `m = 0` cases for D.4.
* **(iv) D.8–D.11** — `D/N8.lean` (interface, done) and its own modules:
  exports `eq81`, `eq274`, `eq277`, `eq299`, `eq305`, `eq307`–`eq314`.
  First task: add the statements (269), (290)–(292), (295), (300)–(302)
  that package (v) cites, and the semantics of `mc` at every width
  (`Λ_c(U)`, extending `Soundness.eval_box` to `zx`, `xz`, `mch`, placement
  and colours) for the semantic steps.
* **(v) D.12–D.13** — `D/N13.lean` (interface, done): exports `eq315`–`eq317`,
  `eq333`, `eq334`, `eq335`–`eq340`, `eq342`, `eq344`–`eq352`.  Internal:
  (318)–(328) (cites (4-, 5-qubit) 214–248, 267, 268 via `eqNNN`).
* **(vi) D.14–D.15 and Appendix E** — `D/N15.lean` ((353)–(360), (361)) and
  `E/*.lean`: Lemma 8.4, 8.5, 8.6 (⇒ `lemma_8_7`), the decoding of each
  rule (⇒ `lemma_8_8`).  Needs: the decoded letters written as `mc` gates
  (`dZZ1 n a = mc n .box [t] …`, by unfolding `placeAt` = `placeG`), Gray
  code facts, the transport of each rule instance to the canonical position
  ((81), (307), (313), (353)).  Rules (20), (21), (25)–(28), (30),
  (33)–(35), (42) decode by definition.

## Status

* Done: `Weak.lean` (weakening, semantic steps, window step), `MC.lean`
  (conventions), `D/N8.lean`, `D/N13.lean` (interfaces, statements only).
* Next: the concrete-width engine and the figure parser (package (i)).
