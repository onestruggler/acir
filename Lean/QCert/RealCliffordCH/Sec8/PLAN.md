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
slow beyond three wires (rational arithmetic, normalised by `gcd`): about 3
minutes for the 40-gate comparison on three wires of `WeakTest`, and more
than 6 minutes (not finished) for its 80-gate one on four (each swap is 9
gates, 6 of them `H`).  Use **`Fast.check`** (`Fast.lean`, `sem_of_fast`):
the same simulation over `ℤ[√2]` as pairs of integers with one power of
`1/√2` per circuit (`H`, `CH`: sums and differences, `CH` multiplying its
control-0 block by `√2`; `Z`, `CZ`: negations), decided as one Boolean.
Times (kernel, `decide +kernel`): 0.7 s for the 3-wire case, 5.4 s for the
4-wire case.  A further factor (swaps as permutations of rows rather than
9 gates) is possible if checks over letter words need it.

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
  at width 3 from Figure 4 and two-qubit completeness, via the engine
  `EngineN.lean` (done, tested in `EngineTest.lean`): words of letters
  `L` (`H j`, `Z j`, `C j` = CZ, `K j` = CH with `H` on wire `j`, `S j` =
  swap, on `N + 1` wires, drawn order, `circW`); steps `rw i k dir` (table
  equation `k`, `AllD`), `sw i` (exchange of disjoint letters,
  `comm_disj`), `sem i len r` (Lemma 5.1 on a window avoiding wire 0 or the
  top wire, decided by `Fast.check` one wire down); `check_sound` turns a
  run decided by `decide +kernel` into a derivation, given `IH (N + 1)`.
  On three wires the table needs only the three-wire rules (12)–(18),
  (f3), (f4) and the definition (8) of the swap; every one- and two-wire
  rule is a `sem` step.  Exports the `m = 0` cases of `eqNNN` for D.2.
* **(ii) D.3 and `n = 4`** — `D/W4*.lean`: (150)–(248) at width 4 from
  completeness on three qubits.  Exports the `m = 0` cases for D.3.
* **(iii) D.4 and `n = 5`** — `D/W5*.lean`: (249)–(268).  Exports the
  `m = 0` cases for D.4.
* **(iv) D.8–D.11** — `D/N8.lean` (interface, done) and its own modules:
  exports `eq81`, `eq269`, `eq274`, `eq277`, `eq290`–`eq292`, `eq295`,
  `eq299`–`eq302`, `eq305`, `eq307`–`eq314`.  The statements (269),
  (290)–(292), (295), (300)–(302) that package (v) cites are in
  `D/N8.lean` (stated, checked numerically by `gen/sec8/iface_n8.py`).
  The semantics of `mc` at every width (`Λ_c(U)`, extending
  `Soundness.eval_box` to `zx`, `xz`, `mch`, placement and colours) is
  `MCSem.lean` (done: `eval_mc`; `eval_mc_blk` for the semantic steps).
  Engine for the schemas: `D/SymEngine.lean` (letters on five local wires,
  semantic steps decided by `D/LSim.lean`, frame from `Net`), tables
  `D/N8/Anchors.lean` ((19), (269), local swaps).  Proved: (81), (271),
  (272)–(277), (280), (285), (286) (`eq81`, `eq269`, `eq274`, `eq277`;
  (280) and (285) in `D/N8/S285.lean`, not by the paper's route), and from
  five wires on (289), (293), (295)–(299) (`D/N8/S299.lean`).  Next: the
  interface `eq299` (four wires needs (166), not yet in `Small`), then
  (300)–(302), (305), (307)–(314), (290)–(292).
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

* `Net.lean` (package (v), done, no `sorry`, no completeness hypothesis): swap
  relations at width `N`; naturality of `placeG`/`mc` under swaps (`mc_swap`,
  `mc_swap_sym` given `CanonSym`, i.e. (307)/(313)/(353) at the canonical
  position); `mc_toTop`, `letter_toTop`, `ToTop`, `liftIdle`, `semIdle` (windows
  idle on a wire `q`); `shift_placeG`, `place1_placeG`, `place2_placeG`.
* Package (v): (315)–(317) proved in `D/N13.lean`.  (318), (319) transcribed and
  checked numerically at widths 4–6 (scratch `t318.py`); their proofs and
  (320)–(328), (333)–(352) remain.

* Done: `EngineN.lean` (the concrete-width engine), `Fast.lean` (the fast checker), `Weak.lean` (weakening, semantic steps, window step), `MC.lean`
  (conventions), `D/N8.lean`, `D/N13.lean` (interfaces, statements only).
* Package (i): `D/SmallDefs.lean` and `D/Small.lean` state every fixed-width
  equation the chain cites (D.2 (117)–(148), D.3, D.4), generated from the
  figures and checked numerically; the `m = 0` derivations are `D/W3.lean`
  (package (i)), `D/W4.lean` (ii), `D/W5.lean` (iii), stated with `sorry`.
  The figure parser `gen/sec8/figparse.py` reads every statement and every
  derivation chain of D.2 (pages 66–79; each step checked numerically, see
  `gen/sec8/README.md`) and the D.3/D.4 statements.  Next: D.2 at width 3
  (`gen/sec8/w3.py` turns the paper's steps into engine runs).
* Package (ii): `D/WEng.lean` (engine over gadget tokens, semantic windows idle on any
  wire, `swp`), `gen/sec8/w4/` (tokens, solver, generator; see its README).  Proved at
  width 4 (`D/W4/A.lean`): (150)–(155), (157)–(159), (161), (162), (164),
  (168), (169); `d157`, `d168` in `W4.lean`.  Next: derived table entries
  (inverses, conjugates) for (152)/(153) and the equations blocked on them, then (177)
  on, the families, D.4.
* Package (vi): `D/N15.lean` stated ((353)–(361), checked numerically by
  `gen/sec8/e/iface_n15.py`; the decoding model `gen/sec8/e/decode.py` mirrors
  `Decoding.lean` and preserves the semantics on every letter at `n = 3, 4`).
  **`lemma_8_7` proved** (`Lemma87Proof.lean`, `E/`), from the interface
  statements (274), (307), (309)–(311), (313), (336) and (353).  Lemma 8.8
  (`Lemma88Proof.lean`, cases by rule): done (20)–(44); open (45), (46).  Lemma 8.5 at every width is
  `E/Lemma85`; (36), (37) are `E/Rule3637` (with `E/Swap36`).
  (360) is `N15/E360`; (361) is `D.eq361` in `E/Eq361.lean` (its proof needs the E toolkit,
  which imports `N15.lean`); (43), (44) are `E/Rule43`, `E/Rule44` (see HANDOVER).

## Package (iv): how to continue

* **Workflow.**  Write the run in `gen/sec8/se.py`'s model first
  (`se_runs.py` has every run so far; `semOK` checks a window on the
  bulk-on and bulk-off blocks), then copy it into Lean as
  `check 4 T w v [steps] = true := by decide +kernel` and
  `check_sound (frame 4) ih (T_ok m ih) run` (width `m + 5`, letters on the
  local wires `0..4`, bulk above).  A run module builds in under a minute.
* **Letters.**  `.g Kd tg cs b`: `b = true` puts the bulk as black controls;
  with no bulk (`m = 0`, the small cases) use `b = false`, or the off-block
  check fails.  The order of `cs` matters for the table matching
  (`DecidableEq`); relabeled letters are written `swapG j …` so that the
  `swapE` table entries match.  A sem step needs every letter of both windows
  to avoid the same *local* wire syntactically; a gate idle on wire `q` only
  semantically is no help (move its box wire with (274)/(277) or carry it
  across a swap with `swapE`).
* **Tables.**  `t19`, `t269` (`Anchors`), `swapE` (not when both swapped
  wires are controls), `qcommE` (`H`/`Z` on a wire passing a letter idle on
  it), and the proved schemas: `s272` (`CZ₀₁` vs `B0` = box `[0]` ctl
  `2,3,4`, wire 1 idle), `s274` (`B1 = B0`), `s276`, `s277`, `s286`
  (`bx0 = V C W C`), `s271c`, `s273` (`CZ₀₂` passes `bx0`; shorter than the
  paper: through (286)), `s274r`, `s275`.  Small widths: two semantic
  steps through an intermediate idle on both wires (`I274`, `I277`), or
  `Small.eqNNN` (`I269` uses `eq126`).
* **Remaining same-width DAG** (read off the proof figures; the extracted
  citation lists miss some): (278) ← (274), (277), (317)ₙ₋₂, (145);
  (279) ← (278), (355)ₙ₋₁; (280) ← (272), (279); (282) ← (280), (18),
  (112), (9), (111) [`P ⊗ P` turns `CZ(box, idle)` into `CH(box ← idle)`];
  (283) ← (282), (272), (274), (277), (285)ₙ₋₁, (303)ₙ₋₁, (148), (82);
  (284) ← (269), (283), (312)ₙ₋₁, (299)ₙ₋₁; (285) ← (284), (281)ₙ₋₁,
  (282); (288) ← (272), (172), (173), (160); (289) ← (271), (272), (81),
  (292)/(301)/(302)ₙ₋₁; (290) ← (288), (157); (291) ← (289), (157);
  (292) ← (269), (287), (139), (140); (293) ← (291), (216), (217);
  (294) ← (269) only; (295) ← (290), (293), (294) and D.3's (209), (218),
  (221)–(226), (240); (296) ← (295), (232)–(235); (297) ← (275), (296);
  (298) ← (285), (297); (299) ← (273), (298), (286).  (300)–(302),
  (305), (309)–(313) then follow from (299), (307) from (275) and (306) ←
  (295).  For (307) with `j ≥ 3` a direct route exists: `W`, `V` are on the
  bottom three wires (structural commutation) and the inner box is idle on
  wire 2, so (307) one width down applies to it (Lemma 5.1).
* **Facts found on the way.**  With `B = W C V C`: `B² = 1` iff `B`
  commutes with `V` iff `B` commutes with `C` (iff (300)); (286) follows from
  (19) alone; `C W C ≈ W B` and `C V C ≈ V B` follow from (286), (269).
  None of these avoids (298).

## Lean takeover checkpoint (2026-10-28)

Work continued from the Lean files and the papers, without consulting
Agda sources. The following interfaces now have checked proof terms:

* `D/N8`: (290)–(292), (299)–(302), (305), (307)–(314). The new modules
  `N8/Low`, `MoreLow`, `ControlFour`, `Below`, and `MergeHg` supply the missing low-width
  instances and connect the existing general proofs. `IFive.hg12_mc`
  was renamed `hg12_circ_mc` to avoid a collision with `I277`.
* `D/N15`: (353)–(357) and (359), connected through `N15/E359`.
* `D/W4`: (160), (172)–(174), (209). The previously generated `W4/B3`
  was recovered and kernel-checked; it supplies (202), (204)–(209).

These remove 27 interface placeholders. This does not certify every
dependency of those interfaces: the remaining placeholders are listed
in the development README. In particular, `N8` still needs the four-wire
case of (295); `N13` has the remaining commutation
interfaces; `N15` needs (358), (360), (361); Appendix A still needs the
two Reidemeister–Schreier hypotheses and Appendix E its remaining cases.

At the project level, `QCert/Table1.lean` imports all sixteen results and
`QCert/Audit.lean` prints their transitive axioms. Check them with
`./check.sh QCert.lean QCert/Audit.lean`. `check.sh` serializes independent
Lake invocations because overlapping builds raced on `.olean` files.

### Continuation on 2026-10-28

Thirteen more interface placeholders are replaced: `W3.d141`, `d142`,
`d143`, `d144`, `d148a`, and `W4.d214`, `d215` (both Boolean instances),
`d221`–`d226`. `W4/B4` contains
the ZX instance of (214), and `W4/Inverse` derives its XZ instance by
expanding a full-width inverse pair into CH and box involutions. The
generator `w4/proj.py` now constructs that cancellation directly;
`w4/gen_families.py` checkpoints successful Boolean instances and tries
existing inverse equations before longer searches. `w3gen.py` includes
explicit plans for (142), (143), (144), and (148a).

`W4/HgMerge` proves the merge of complementary controlled Hadamards from
the box merge, generated by `w4/gen_hgmerge.py`. This supplies the missing
prerequisite for (210)–(213), now proved in `W4/Expansion`, which also
proves (215), (221), (222), and (225). `W4/AvailFull` adds the control
symmetries of full-width ZX/XZ, and `W4/MergeZX` uses them for (223),
(224), and (226). `gen_families.py` selects these symmetries when
`AvailFull` is among its previous modules.

The large-width proof `N13/E320.t295` uses `N8.eq295_5` directly, avoiding
the open four-wire branch of the general interface. The axiom audit also
checks the new interfaces and the existing large-width commutation
lemmas (335), (336), and (340). The latter three were checked to use only
standard axioms. The four-wire case of (295) remains open.

The existing parsed D.3 chain for (216) disagrees numerically with its
endpoints at its first and last steps; its internal steps agree. This is
a problem to investigate in the transcription, not a proved paper error.
`gen_families.py` now rejects inconsistent parsed chains before searching
them. This numerical filter never accepts a Lean proof; all certificates
still go through the kernel. No theorem statement was weakened.

Validation: `./check.sh QCert.lean QCert/Audit.lean` passed (4011 jobs).
All thirteen new interfaces and the three audited large-width commutation
lemmas have only standard axioms. Across the 54 audited declarations,
only the three already-open Table 1 results contain `sorryAx`. There are
68 proof placeholders left in the project (60 standalone and eight rule
branches), down from 81 at the start of this continuation. Build logs and
the audit summary are in `.lake/takeover/continue-final-check.log` and
`.lake/takeover/table1-axioms.txt`. A further generated candidate for (220)
is saved in `.lake/takeover/CandidateLate.lean`; it is not yet kernel-checked
or connected to `d220`.

### Continuation on 2026-10-29

Twenty-four more placeholders are replaced: `item_a`, `W4.d216`–`d220`,
`d227`–`d241`, and `d246`–`d248`. All their modules and public interfaces
have passed Lean's kernel checks. There are 44 remaining proof sites in
the project: 36 standalone placeholders and eight branches of Lemma 8.8.
The four-wire interface now has only (242)–(245) open.

`A/ItemAProof.itemA_hh` uses fresh indices, the frame action, and the
contraction from (66)/(71); `item_a_proof` combines all four generator
cases. `Thm410Proof.item_a` now uses that proof.

For four-wire rotations, expanding a partial rotation into CH/CZ factors
and tracking reversals gives (216)–(218), independently of the problematic
parsed chain. The conjugated Hadamard relation (203) is also proved:
step 18 reuses step 4 backwards inside a cancelling pair of `P ⊗ P`.
This supplies (219). `gen_conjrotation.py` selects the two separate
branches of the paper's proof of (228), according to its Boolean colour.

The 64 cases each of (240) and (241) follow from a few commutations,
merging complementary controls, cancellation, and colour changes.
Equations (247)/(248) follow by conjugating white-controlled CZ to CH,
using (229), (230), and (232)–(235). Their generators are
`gen_fullrotation.py`, `gen_samerotation.py`, and `gen_whitecz.py`.
`solve2.conj_down` now explicitly proves equality when relabeling merely
changes control-list order. No theorem statements or axioms changed.

The full build and Table 1 axiom audit are being rerun after these changes.
The previous full check (4027 jobs, before the last ten replacements)
passed and confirmed only the same three open Table 1 declarations.


### Verified three-wire progress, 2026-10-29

`W3.d139`, `d140`, `d145`, `d146`, and `d147` are now proved. The
existing completed derivations live in `W3/Base.lean`; `W3/Tokens.lean`
uses only those derivations, the Figure 4 axioms, and smaller-width
completeness. Its token runs and endpoint bridges passed kernel checking
(2178 jobs). The three-wire interface has only `d148b` left open.

For (139), changing the control order by (14) exposes a cancelling CZ;
the middle of the diagram chain supplies a reusable commutation. The
final step of (146) follows by reversing its proved prefix and commuting
the central Z. The full 63-step chain of (147) then uses (146).

`W4/ConjCommBase.lean` supplies five checked base cases for (242), (243),
and (244); their Boolean families are still being constructed, so the
public `d242`--`d245` declarations are still open. In (244), a repeated
commutation in the paper is extracted as `t244Pass`.

There are now 39 proof sites left (31 standalone and eight rule branches).
The full audit after the preceding batch passed (4031 jobs); the audit
for this batch passed (4034 jobs), including the five new W3 results and
the W4 base cases; all ten have only standard Lean axioms.
Table 1 remains at 13 of 16 complete rows. No Agda source was consulted.
The user requested pushes after each verified batch and six further
hours of work, starting at 2026-10-28 16:50 UTC.

### Four-wire equations completed, 2026-10-29

All Boolean cases of `W4.d242`–`d245` are now proved, completing the
four-wire interface. The certificates use the six checked base cases,
inverse cancellation, colour conjugation, and earlier four-wire equations.
The full build and axiom audit passed (4038 jobs); all four declarations
depend only on standard Lean axioms. There are 35 remaining proof sites
(27 standalone and eight rule branches), and Table 1 remains at 13 of 16
complete rows. No Agda source was consulted.

### Three general commutation interfaces completed, 2026-10-29

`eq335`, `eq336`, and `eq340` are proved at every stated width. The new
three-wire and four-wire cases use only the earlier equations and the
stated smaller-width induction hypothesis. The four-wire box cases use
the expansion (150), complementary-control merging (170), and (179),
(180); controlled Hadamards follow by conjugation with `P ⊗ P`.

The complete build and axiom audit passed (4041 jobs), with no `sorryAx`
in these three results. There are now 32 remaining proof sites (24
standalone and eight rule branches). Table 1 remains at 13 of 16 complete.
The generators are `gen_boxcomm_low.py`, `gen_comm_three.py`, and
`gen_comm_low_interface.py` in `gen/sec8/w4`.

### Five-wire foundation checked, 2026-10-29

`W5/Base.lean` checks 19 certificates: the auxiliary equations
(249)–(260), colour variants needed by them, and base cases for (267),
(268). The build passed (2177 jobs, 205 seconds for the new module).
The axiom audit of (249) and the two main base cases reports only standard
Lean axioms. Their complete Boolean families are being checked separately;
the remaining-interface count is still 32 at this checkpoint.

### Opposite-control commutation checked, 2026-10-29

`N13/BoxPPIdle.lean` and `BoxPPBridge.lean` prove that two boxes with
opposite controls on wire 2 commute when one is conjugated by `P ⊗ P`.
The bulk controls may have independent colourings. The semantic calculation
uses the verified symbolic evaluator on three local wires; an idle wire
then permits the smaller-width completeness hypothesis to give a circuit
derivation at every width from five. Both modules typecheck, and the
`commBBpp` axiom audit contains only standard Lean axioms.

### All cases of five-wire equation (267) checked, 2026-10-29

`W5/Family267.lean` supplies all 32 combinations of the five Boolean
parameters of (267). Lean completed the module in 1448 seconds. Its first
and last exported cases have only standard Lean axioms. The companion
family (268) is still checking before the shared `W5` interface is audited.

### Small-width equation (337) checked, 2026-10-29

`W4/BoxHgLow.lean`, `N13/ThreeHg.lean`, and `N13/LowHg.lean` prove
equation (337) on three and four wires, for every allowed colouring.
The four-wire cases with a white control in front of the Hadamard use
complementary-box merging and the previously proved controlled-Z
commutations. The modules typecheck and both exported small-width results
have only standard Lean axioms.

### Colour-product and borrowed-wire lemmas checked, 2026-10-29

`N13/ThreeHg338.lean` and `LowHg338.lean` prove all three-wire cases
of (338), and its four-wire cases with different bulk colours.
`MergeAll.lean` proves the product over every colouring merges into the
box with those controls removed, and isolates the final all-black factor
when the other factors commute. `HgBorrow.lean` proves the small box and
the borrowed-wire X commute with the all-black controlled Hadamard.
All four modules typecheck; the five exported results audited here have
only standard Lean axioms. The full arbitrary-width (338) is still pending.

`E338Merge.lean` now completes the equal-colour case from the different-colour
case at any width. Instantiating this with the checked finite cases gives
`LowHg338Complete.comm338_all_4`, including every colouring on four wires.
Its axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`.

### Equation (345) complete, 2026-10-29

`N13/E345.lean` and `ThreeHg345.lean` prove the commutation of the two
controlled Hadamards, with arbitrary bulk colours, at every width from
three. Above three wires this is the already proved box commutation (336)
conjugated by `P ⊗ P`; the swap of the two bottom wires commutes with that
conjugating circuit. The three-wire cases use (133), (134), and colour
conjugation. `D.eq345` now uses this proof, and its axiom audit is clean.
This removes one more interface admission: 31 remain at this checkpoint,
before integrating the five-wire families currently being checked.

### Five-wire families complete, 2026-10-29

`W5/Family268.lean` passed its kernel check in 2119 seconds. The shared
`W5.lean` interface now proves (267) and (268) for all Boolean parameters;
both exported statements have only standard Lean axioms. Together with
the completed (345), this leaves 29 proof sites in the requested
development (21 standalone and eight rule branches). Table 1 remains at
13 of 16 complete rows. No Agda source was consulted.

### Package (v), second session, 2026-10-29: drafts, not built

(337), (338) from five wires on and (339) from six wires on are written in
`N13/E337*`, `E339*` and `Loc5` (imported by nothing; `eq337`, `eq338`,
`eq339` unchanged).  Building them is blocked on memory: `E322`, which
`E337` imports through `E322x`, needs about 11 GB, and a declaration deciding
four 22-letter semantic windows passed 4.7 GB.  `HANDOVER.md` (package (v),
second session) has the analysis, the wiring for `N13.lean` and the plan for
the rest of the package.

### Package (v), fourth session, 2026-10-29

Built and wired: (339), (342), (344) from six wires on (`N13/E339b`,
`E344s`, `E344t`, semantic separation, no decided window), (333), (334)
(`N13/E333`, given (339) at the same width) and (346) at every width
(`N13/E346`).  `eq339`, `eq342`, `eq344` keep one `sorry` branch for widths 4
and 5 (another agent, `N13/Low339*` etc.).  Open: (347)–(352); the plan is in
`HANDOVER.md` (package (v), fourth session).
