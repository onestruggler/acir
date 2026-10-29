# Handover (2026-10-29)

State of the Lean formalization of Table 1 of `qcert.pdf`, written when the
Claude session that ran eight parallel work streams on 2026-10-28 stopped (all
of its agents hit the account's session limit around 19:30). Someone else
(Astra) began integrating the streams' files around 23:50; check `git status`
and `git diff` before trusting anything below about a particular file.

## Rows

| Row | State |
| --- | --- |
| Rows 1–11, 14 (Greylyn … Clifford+T, Toffoli–Hadamard) | proved, no `sorry` (unchanged) |
| Li et al. [2025], qutrit Clifford | **proved** (Theorem 4.4 at every width; commits 2a7787b5, cdf9ddad) |
| Blake [2026], six fragments | Theorem 22 (5) on two and three wires written by the `cliffcs2` stream (uncommitted, see below); rests only on Clifford+CS's `rsData` |
| Bian–Selinger [2023], three-qubit Clifford+CS | `rsData` open; design only (`cs3` stream) |
| Clément [2026], real Clifford+CH | Theorem 4.10 proved; Lemma 8.8 and the Appendix D interfaces partly proved (uncommitted) |

Everything the streams wrote after commit cdf9ddad is uncommitted in the working
tree. The streams were told not to edit interface files (`W3/W4/W5.lean`,
`N8/N13/N15.lean`, `SmallDefs`, `Small`), so the edits to those files are the
integrator's.

## Rules the streams followed

* Work from the source papers and the Lean code only, never from the
  repository's Agda formalization (everything outside `Lean/`).
* Papers: arXiv 2602.06644 (Clément), 2306.08530 (Bian–Selinger 3-qubit
  Clifford+CS), 2602.09874 (Blake), 2204.02217 (Bian–Selinger 2-qubit Clifford+T,
  Reidemeister–Schreier), 2508.14670 (qutrit). Fetch PDF and TeX source with
  `curl https://arxiv.org/pdf/<id>` and `https://arxiv.org/e-print/<id>`.
* Build in WSL with `./check.sh QCert/Path/Module.lean`; `.lake` is a symlink to
  `/home/bones/qcert-lake` (Mathlib from the cache). WSL `python3` has numpy,
  pymupdf and sympy.
* No `sorry`, `native_decide` or new axioms in finished work; `QCert/Audit.lean`
  prints the axioms of every row's theorem.
* Files under `Lean/` are LF (`.gitattributes`); do not convert them to CRLF.

## The streams' working notes

Copies of each stream's brief, status file and scratch folder are in
`Lean/.handover-scratch/` (untracked, ignored by git): `briefs/`, `status/`,
`BRIEF-COMMON.md`, and the scratch folders `thm410/`, `n8/`, `n13/`, `rcch-e/`,
`rcch-fixed/`, `cs3/`, `cs2/`.

### Blake, CliffCS₂ on two and three wires (`cliffcs2`)

* Two wires: `Minimality/CliffordCS/W2Data` (generated), `W2Blocks`, `W2Rels`,
  `W2Lemmas` (generated), `W2Complete` (`complete₂_of_source`). Generators:
  `gen/cs2blk.py`, `cs2abs.py`, `cskb.py` (Knuth–Bendix with proofs),
  `run_cskb.py`, `run_cs2.py` (cache `cs2_cache.txt`), `gen_cs2.py`; regenerate
  with `python3 run_cs2.py && python3 gen_cs2.py data rels lemmas`.
* Three wires: `W3Base`, `W3Lemmas`, `W3Rels` (generated), `W3Complete`
  (`complete₃_of_source`), from `gen/run_cs3.py` (cache `cs3_cache.txt`),
  `gen_cs3.py`; two-wire steps go through `complete₂`.
* `Theorems.lean`: `cliffordCS_complete_of_source` (widths 0–3) and
  `cliffordCS_complete` with no `sorry` of this folder (`sorryAx` only through
  `QCert.CliffordCS3.theorem_3_1`, i.e. `rsData`).
* Left to do: `W3Base` builds in about 200 s (the 8 × 8 checks `e_ok`), so speed it up
  or split it; update the Minimality README; run a final build and axiom check.

### Three-qubit Clifford+CS, `rsData` (`cs3`)

Nothing in Lean yet. Design, with Python in `CliffordCS3/gen/` (`core.py`,
`design.py`, `engine.py`, `fig2.py`, `two.py`, `tc.py`, …):

* Reidemeister–Schreier through a *macro* coset action. The macro letters are
  Coxeter tokens `t_d` along the Gray path 5, 4, 0, 1, 3, 2, 6, 7. The atoms are
  `Z = i_[7]` and `K = K_[6,7]`. The coset representatives are `ε` and `i_[7]`.
  The action is `h c y := hstar_macro c (enc y)`.
* Hypothesis (b) splits through `rs_claimB` into B1 and B2:
  * B1, macro derivations, which are combinatorial (frames, S₈ normal forms);
  * B2, about 70 three-qubit identities (macro axioms × cosets), each needing a
    searched derivation from Figure 2.
* Phase A, started: completeness on two qubits (`U₄ = CS(2)`, one coset) as a
  tool for semantic two-qubit steps.
* The two-qubit Clifford+T row (`QCert/CliffordT2`: `Cosets`, `Cert/`,
  `FastRewrite`, `Eqs/`) is the template for checking such derivations in Lean.
* Do not use the authors' Agda code (it is what the repository's Agda port copies).

### Real Clifford+CH, Theorem 4.10 (`rcch-thm410`)

Done: `Sec8/Thm410Proof.lean` has no `sorry` (`theorem_4_10`).

* Item (a): `Sec8/A/ItemAProof.lean` (`item_a_proof`).
* Item (b): `Sec8/A/ItemBProof.lean` (`item_b_proof`), through Clément's relations
  (`QCert.Clement2019`, proved equivalent to Figure 6 syntactically):
  * `ItemBCon`: `GB n := rsCon (tauA n) (Fig8 n)`; (a1)–(d2) in `GB` by `good_frame`
    and `ItemBPhi`'s `img_*` (tags chosen away from the relation, `exists_tags`).
  * `ItemBChk`: a checker for chains at `Fin m` whose steps are (a1)–(d2), extra
    equations, or semantic identities on `K` indices (decided over `ℤ√2`);
    `ItemBPull`: the pullback of `GB` along an increasing map contains the
    semantic identities on `K ≤ 5` indices (completeness of Figure 6 on `K`
    indices, given (d3)).
  * `ItemBRen8`: conjugating a Figure 8 equation by a Hadamard-free word renames it.
  * `ItemB20`: Clément's (20) at increasing pairs, from (45) through the frame.
  * `ItemBd3`: (d3) at both orders of the middle indices from (20), chains
    `chA`, `chB` (the printed derivation of Lemma A.1 split into steps on three
    indices).
  * `ItemBRel`: Clément's (1)–(19) in `GC n := GB.comap tr` by his tables
    (`ToFig6`), and `GC n` invariant under permutations (`gc_perm`).
  * `ItemB46`: the relation of (46) at the indices `2, …, 7`, directly: away from
    `0, 1` the coset action is a frame with pair `0, 1` (`hstar_psi`), and the
    images are (46) renamed by the even permutation `(0 2 5 7)(1 3 4 6)`. This
    works at `n = 3`, where a frame with three tags does not fit six indices.
  * `ItemB21`: Clément's (21) from it by a chain with steps on five indices (`ch21`).
* The chains were generated and checked numerically by the Python in
  `.handover-scratch/thm410/ib/` (`core.py`, `chain.py`, `lib.py`, `way.py`,
  `emit.py`, `simlean.py`; `d3gen.py` + `gend3.py`, `c21.py` + `gen21.py`).
* `ItemASteps.lean`, `ItemBFun.lean`, `ItemATest.lean` are older and unused.

### Real Clifford+CH, fixed widths (`rcch-fixed`)

* `Sec8/D/W3/Sym.lean`: relabelling, (81) and swap table entries, `canonSym_small`.
* `Sec8/D/W4/Avail.lean`: `CanonSym` for `box3` and `hg2`, `havail4a`.
* `Sec8/D/W4/B1.lean` (52 s): (156), (160), (163), (165)–(167), (170)–(176); exports
  `e160`, `e172`, `e173`, `e174`.
* Solver in `gen/sec8/w4/` (`sym.py`, `solve2.py`, `proj.py`, `gen_b.py`, `gen2.py`).
* Next was B2, (177)–(213), then the rest of D.3 ((214)–(248)), the open
  `d139`–`d148b` at width 3 and `d267`, `d268` at width 5 (check what the integrator
  wired since).

### Real Clifford+CH, Lemmas D.8–D.11 (`rcch-n8`)

All of the following build, at every width `m + 5` unless noted:

* Five local wires: `Sec8/D/N8/Kit`, `S300`, `S290`, `HgPP`, `S314`, `IFive` (`eq290_5` …
  `eq305_5`, `eq307_5_12`), `I307` (`eq307_all`, every width ≥ 3), `I309`, `I310`
  (`eq310_of` for N ≥ 5, `eq312_of` and `eq313_of` for N ≥ 4), `D9` (generic Lemmas D.9/D.11).
* Width 3: `T3`, `T3b`, from Small's (117)–(138).
* Python model: `gen/sec8/se_n8lib.py`, `se_n8runs*.py`.
* Remaining:
  * width 4 for (290)–(292), (295), (299)–(302), (305), the D.9 bases at width 4,
    and (310)₄. (295)₄ needs D.3's (209), (217), (218), (221)–(226), (240) from
    the fixed-width work.
  * a final assembly with the interface names.

### Real Clifford+CH, Lemmas D.12–D.13 (`rcch-n13`)

* The stream was fixing `E335` and `E336a` (`wW`/`wV` need `N8.` qualification).
  New files appeared in `D/N13/` (e.g. `E336x`, which `Audit.lean` imports).
* Plan: from N ≥ 5, (335), (336) with x = y, and (340); then (336) with x ≠ y through
  the relabellings of `E318g`; then the small widths 3 and 4; then (337), (338),
  (345), (339), (342), (344), (333), (334), (346)–(352).

### Real Clifford+CH, Lemma 8.8 and D.14–D.15 (`rcch-e`)

* Fixed `E/Rule24`. `Lemma88Proof` and `RealCliffordCH.Theorem` build again.
* New proofs:
  * rules (38) and (39): `E/Rule38` (`E.dec38`) and `E/Rule39` (`E.dec39`), wired;
  * (353)–(357): `D/N15/E353c`, `E354c`, `E355c`, `E356b`, `E357b` (`D.N15.eq353` …
    `eq357`).
* Refactor: `E/TransportCore.lean` holds Transport without N15, and `E/Transport.lean`
  keeps only `mcSwapAll`. Lemmas such as `bitsOn` moved from `Merge.lean` to
  `TransportCore`.
* Next: (359); rules (40), (44), (31); (358), (360), (361); rules (43), (36),
  (37), (45), (46).

## Remaining `sorry`s at the time of writing (`grep -cw sorry`)

`CliffordCS3/Completeness.lean` (rsData) · `Sec8/Lemma88Proof.lean` 2 ((45), (46)) · `Sec8/D/N13.lean` 19 · `Sec8/D/N15.lean` 3 · `Sec8/D/N8.lean` 1 ·
`Sec8/D/W3.lean` 6 · `Sec8/D/W4.lean` 5 · `Sec8/D/W5.lean` 3.

### Package (vi), second session (`rcch-e`, 2026-10-29)

Files: `Sec8/D/N15/E358.lean` (imported by `N15.lean`, which now proves
`eq358`), `Sec8/E/Rule40.lean`, `Sec8/E/Rule31.lean` (imported by
`Lemma88Proof.lean`, whose cases (31), (40) are now proof terms).
Numerical models in the session scratch (`m358.py`, `m40.py`, `m31.py`,
`m360.py`, built on `gen/sec8/mc.py`'s `mc_sem`); every claim below was
checked there first.

* **(358)** (`E358.braid358`, `eq358'`), not the paper's route.  `a` = the
  `XZ` on wire 0, `b` = the `ZX` on wire 1, `G = CZ · swap` on wires 0, 1:
  `G G = 1`, `G a G = b` (swap, then (357)); the `XZ` on wire 0 controlled by
  wire 1 alone is `a P` ((354) over all colourings of the wires 2…,
  `mergeListZ`), `P` passes `a` ((351)) and `b` ((352)); on two wires
  `a₂ G a₂ G a₂ = G` (decided, lifted by `der_atBot`).  `braid_of_merge` (any
  monoid) gives `a b a = b a b`; work in `(conGen (theory N)).Quotient`
  (`q_of`, `of_q`, `Con.coe_mul`).
* **Rule (40)** (`E.dec40`), the paper's chain: (333) with controls 1, 2
  exchanged (swap) and coloured (`z333`; `X` on the box wire via `xbox` =
  (315) with any colours, moved by a frame; `placedBy_xAt`), (309) at box
  wire 2 (`merge40`), the merged box passes the gadget (`bi_hg`: (274)
  framed by `[0, 2]` from `move274`, (309), (338)), (312), (311).
* **Rule (31)** (`E.dec31`), both `c > a + 1` and `c < a`: far boxes pass
  `R` (`box_rot_comm`: (346)/(347) with `gray_separated`); `B_{a±1}` (box on
  another wire, controls those of `R` except on `R`'s target) conjugates `R`
  into `R⁻¹` (`box_inv_rot`: `N15.bx_z1` moved by the swap of wires 0, 1,
  coloured by (81), (315), `tflip0`); `rot_sq` ((355)), `rot_inv` ((317));
  `rule31_up`/`rule31_down` are the monoid identities.
* Pitfalls met: `D.xs_inv` is in namespace `D`, not `D.N13`; `move274` takes
  its width as `(N := …)`; a theorem inside a `section` with `include ih`
  takes `ih` even when unused (use `omit ih in`); `rw [← h]` with `h : … = G`
  rewrites every `G`, including those inside `set` abbreviations created
  before the goal (use `Eq.trans ?_ h`); `simp only [S8, …]` unfolds an
  abbrev of `List.range (M + 1)` that `List.range_succ` then splits.

**(360), a reduction found and checked numerically (`m360.py`), not yet in
Lean.**  With `a` = the `ZX` on wire 1 (controls 2…, wire 0 idle),
`Bx` = `D.Bx N` (box on wire 0, controls 1…) and `Hg01` = `mc N .hg [0,1] (blackOn 2 N)`:
`Hg01 = PP Bx PP` (this is the definition of `mch`, via `mc_canon`), and
`a = Bx Hg01 Bx Hg01` (monoid order), so `a = (Bx PP)⁴` and
`PP a PP = (PP Bx)⁴ = a⁻¹` by `PP² = 1`, `Bx² = 1` ((299)) and (317).
The one non-trivial input, `a = Bx Hg01 Bx Hg01`, is not a semantic step
(every wire is used).  A route for `N ≥ 4`: (333) one width down, lifted
past the idle wire 0 (`Net.liftIdle` with `ToTop.mc` and the derivation
`D.eq333 (N-1)` itself, no semantics), gives `a = Hg[3,1](ctl 2,4…) · Bx[2](ctl 1,3,4…) · Hg · Bx`;
move both box wires to wire 0 by (277) framed by `[0,3,1]` and (274) framed
by `[0,2]` (as `E.bi_hg` does); then `PP Hg[0,1](ctl 2,4…) PP = Bx[0](ctl 1,2,4…)`
and `PP Bx[0](ctl 1,3,4…) PP = Hg[0,1](ctl 3,4…)` are the definition of
`mch` one width down (lifted past the idle wire 3, resp. 2), and the result is
(334) in the frame with the controls 2, 3 exchanged, moved the same way.
`N = 3` is Small's (129).

**Rules (43), (44)** both need (360) and (361).  (44) is then short:
`D(X03X12) = [box[0](1b, 2…w), XZ[1](2…w)]` by (361); the box passes the
gadget by (338) (`eq338 N _ ih (fun _ => false) (fun _ => false) true`); the
gadget `hg[1,0]` is `PP · box[1](0b, 2…w) · PP`, `PP` turns the `XZ` into a
`ZX` ((360), coloured), and the box passes the `ZX` with wire 0 idle after
splitting it by (354) ((346) for each half).  (361)'s proof uses Lemma 8.5
for `D((-1)[0]X[0,3])` (one instance: the recursion `dZXab` unfolds it into
five letters).

Remaining sorries of package (vi): `N15.eq360`, `eq361`; `lemma_8_8` cases
(36), (37), (43)–(46).  (36)/(37) need Lemma 8.5 (D(E(swap)), D(ℰ(X)));
(45), (46) follow the paper's chains through (333)–(339), (309), (274),
(311), (312).

### Package (vi), third session (`rcch-e`, 2026-10-29)

Proved and wired (commits 86062afb, 5fdd8135, 811d6077, 1cf7e73f); every
step checked numerically first (`gen/sec8/e/m360b.py`, `m361.py`, `m43.py`,
`m44.py`; the second session's `m31`, `m358`, `m40`, `m360` are there too):

* **(360)**, `D/N15/E360.lean` (`eq360_ge4`, `eq360_3`), not the paper's
  route: (333)/(334) one width down carried past the idle wire `0`
  (`liftIdle`, `toTop_mc'`), box wires moved to wire `0` by (277)/(274) in
  the frames `[0,3,1]`/`[0,2]`, then `P ⊗ P` on `0, 1` exchanges box and
  multi-controlled `H` (Definition 2.4 one width down, past the idle wire
  `3`, resp. `2`: `pp_box`, `pp_hg`), and the swap of the wires `2, 3`
  matches the result with (334).  Three wires: (129) by a token run.
  `N15.lean` now has no `sorry`.
* **(361)** is `D.eq361` in **`E/Eq361.lean`**, no longer in `N15.lean`: its
  proof needs `E/Rule31`'s toolkit, and `E/Transport` imports `D/N15.lean`,
  so `N15.lean` cannot import it.  Lemma 8.5 for `D((-1)_[0]X_[0,3])` by the
  paper's argument: `mergeListZ` over the wires `1, …` writes the
  single-qubit `XZ` on wire `0` as `P · X₀ᵇ · X₀ʷ` (`x61`), every factor of
  `P` commutes with the rotation by (352) (`f61_comm`, `bitsOn_black`), and
  (359) under the swap of the wires `0, 1` recolours (`h359_61`); then
  (355), `box_inv_rot`, (311), (317), (354) (`mergeAtZ`: (354) at any
  target, from `mergeCZ`), assembled by `alg361` in the quotient monoid.
* **Rule (44)**, `E/Rule44.lean` (`dec44`): (361), (338) for the box, and
  for the `XZ` the paper's (112), (360), (354), (346) with black controls
  (`xi_g_black`), coloured by (81) at the end (`xi_g_white`).  Tools:
  `hg_pp44` (Definition 2.4 at every width; on three wires the rule (18)),
  `sw_pp44` ((112), a two-wire step), `gadget_pp44` (`G = P Bq P`).
* **Rule (43)**, `E/Rule43.lean` (`dec43`): the paper's chain in the frame of
  `P = P ⊗ P₀₁` — `G = P Bg P`, `A = P A'' P` (`hg_frame`: Definition 2.4 in
  the frames `[2,0]`, `[2,1]`; `klein43`: `P₂₀P₀₁ = P₀₁P₂₀ = P₂₁` from (130)
  by two token runs on three wires), `Bg = R R`, `R A'' = A'' Ri` ((333),
  (334) under the swap of the wires `0, 1`, coloured by (81) and (316) in
  the frame `[2,1]`: `ra43`), (349) in the frame `[2,1]` (`a2_zw43`), (354),
  (360) — so `G A = Zi A Xi`; then, not the paper's end, `B0 Zi B0 = Xi`
  gives `Y = Xi B0 = B0 Zi` and `Y A Y = B0 G A B0 = G A` by (338)
  (`alg43`).

Reusable kit in `E/Rule43`: `colr43` ((81) on a list of wires),
`conjP_colour` (colour an equation `P a P = b` by an involution commuting
with `P`), `colour43` (black → white: `X` on wire `2`, then `U3` on `3, …`),
`sw0_43` (the swap of wires `0, 1` on `mc`), `x2_81`, `u3_col`,
`ctl_1_1`/`ctl_0_1`/`ctl_3_0` (`ctlOf` against `ctlOr`/`colOn`), the macro
`ctl43` (pointwise control equalities: unfold, `split_ifs`, `omega`).

**Lemma 8.8 is now open only at (36), (37), (45), (46).**

* **(45)** (`gen/sec8/e/m45.py`): the decoded letters are
  `E1 = D(H_[0,1]H_[7,6]) = hg[2,0](1○, 3…○)` (`H` on `0`, box wire `2`),
  `E2 = D(H_[0,3]H_[1,2]) = hg[0,1](2…○)` and `Bw = D((-1)_[0](-1)_[1]) =
  box[0](1…○)`; the decoded rule is `E1 E2 E1 Bw E2 = E2 Bw E1 E2 E1`
  (monoid order) — exactly (146) with every wire above `2` a white control.
  All letters are involutions, so it says `K = E1 E2 E1 Bw E2` is an
  involution.  On the subspace `w₂ = 0` it is the two-qubit identity of
  (146); on `w₂ = 1` it is trivial (`E2`, `Bw` act as the identity there).
  No Lean yet.  The `P ⊗ P`-frame tools of `Rule43` (`hg_frame`,
  `klein43`, `hg_pp44`, `gadget_pp44`, `p360w`) should carry over.
* **(46)**, **(36)/(37)**: untouched this session; the second session's
  notes above still apply.

Pitfalls met (besides those above):

* A lemma in a section with `include ih` takes `ih` even when unused, so
  callers must pass it; mark helpers that do not use it `omit ih in`.
* Give `(M := M)` when no argument pins the implicit width (controls such
  as `ctlOr … (blackOn 2 (M + 3))` do not).
* When a derivation's sides are `mc` gates, give `via_conj`/`colour43`
  their lists explicitly (`(l := [Rb43 M])`) and present the derivation as
  `drawn [x] = x` (`D.N15.drawn_one'`): otherwise Lean unifies `drawn ?l`
  with `mc …` by unfolding `mc` into its `colourW` list.
* `simp` does not decide `j + 1 + 1 + 1 < 3` inside `liftW`/`tau`; a macro
  `simp only [defs]; split_ifs <;> first | rfl | (exfalso; omega)` does.
* `omega` treats `2 ^ (M + 3)` and `2 ^ (M + 2 + 1)` as different atoms
  (`tOf_eq` produces the second): state the bound in both forms.
* Python heredocs passed through the Bash tool broke on some `'`; write the
  script to a file first.
* Memory (coordinator's note): one decided run per declaration,
  `set_option Elab.async false` where a module decides several.  The runs of
  this session are small (`E360.run360`, `Rule43.runK1`/`runK2`,
  `Eq361.zx61`: two- and three-wire); every module here builds in under 10 s.

### Package (v), Lemmas D.12–D.13, continued (2026-10-29, second session)

Nothing new is proved; no interface `sorry` was removed.  Written (all new
files under `Sec8/D/N13/`, imported by nothing, none built):

* `E337.lean` (+ `E337c`, `E337r1`, `E337r2`): (337), and (338) with
  `x ≠ y`, from five wires on, by the template of `E336x`.  Once built, the
  replacement for `N13.lean` is: import `E337`, `LowHg`, `LowHg338`,
  `E338Merge`; `eq337` by `comm337_3`, `comm337_4`, `comm337_ge5`; `eq338` by
  `comm338_from_diff N hN ih (diff) (fun x y => eq335 N hN ih x y) x y c₁` with
  `diff` by `comm338_3`, `comm338_4`, `comm338d_ge5` (cases `N = 3, 4, ≥ 5`).
  That closes both at every width.
* `E339.lean` (+ `E339a`, `E339r1`–`E339r3`): (339) from six wires on
  (`comm339_ge6`).
* `Loc5.lean`: `loc5`, an equation between two words of local letters on the
  five wires `0–4` holds from six wires on as soon as `SE.lcheck 5` decides
  it (completeness on five wires + `Loc.der_loc`); the step the engine cannot
  take inside a run.  (Its first build failed on a stray `exact` after
  `congr 1`, now removed; not rebuilt.)

**Why nothing is built: memory.**  The VM has 12 GB shared by four agents.
`E322` (committed earlier, imported only through `E322x` by `E337`) takes
**about 11 GB** to build (measured: 11.2 GB resident before it was stopped);
its runs `chk_inner322` and `chk322` are decided in single declarations.
`E337r1`/`E337r2`, one declaration of four 22-letter semantic windows each
(`decide +kernel` on `check 4 [] …`), passed 4.7 GB within two minutes.  So
an engine `sem` step on four local wires costs over a gigabyte in the kernel,
and a run of several of them in one declaration is not affordable here.
Before building any of these files:

1. Split `E322`'s runs one Boolean case per declaration (the five Booleans
   `one a α β γ`; `T322_ok` and `r322` then case on them), and measure.
2. Split `E337r1`, `E337r2`, `E339r1`–`E339r3` to one run (one choice of the
   rotations as well as of the Booleans) per declaration: change
   `gen_split.py` (in the session scratch; simple to rewrite: one
   `theorem name_<tag> : <statement> := by decide +kernel` per case, and a
   combining theorem by `cases`).  If one run still needs several GB, replace
   the rotation-against-rotation steps by a semantic lemma (the two gates act
   on the subspaces where the separating wire is `1`, resp. `0`; prove the
   commutation from `MS.eval_mc` as `Sem.sem_box_comm` does for boxes, then
   `semIdle` on a bulk wire) instead of deciding windows.
3. Build with a memory watchdog (a loop killing this package's `lean` above
   about 4.5 GB; `ulimit -v` breaks `lake`, which then cannot create
   threads).

**How (339) is done (reuse it for (342), (344)).**  `sep_reduce` (lo = 3)
puts the difference of the colourings on wire `3`; the swap of the wires
`2, 3` carries the pair to the frame of `E336x` (`AE` = the box on wire `0`,
separating control black on wire `2`; `BE` = `hg[1,3]`, white on wire `2`).
`AE` is expanded by `expX`.  `BE = M · box · M'` (`expBE`), `M = S₀ S₂ S₁
(P⊗P) S₁ S₂ S₁` (the letters `mL`, `mL'`): three swaps take `hg[1,3]` to
`hg[0,1]`, `hg0_box4` writes it as `P⊗P` around the box, and the
transposition `(1 3)` (`S₁ S₂ S₁`) puts the black control of its `H` wire on
wire `3`, so that `expX` idles the `H` wire.  The pairs: two rotations, one
semantic step without wire `4`; `A`'s rotations against `B`'s remainder: `M`
carries the remainder to `box[1](0:c₃, 2○, 4…)` idle on `3` (`remB`, through
(276) in the middle, `pp_box276` from `N8.s276`), then `E336x.commRBs`; the
remainders by `E336x.commBBs`; `A`'s remainder (idle on wire `3`) against
`M r M'` by `gcl`: an engine run re-expanding the remainder with the triple
`1, 2, 4` (one semantic step without wire `3`), whose four five-wire steps
come from `loc5`.  That pair is the only one needing six wires.  Only the
rotations `P1`, `P2` are decided; `P5`, `P4` are their inverses (`chkInvR`,
`chkInvS`, `comm_bases`, `comm_basesC`, Lemma B.5).

* (344): `A = hg[0,1](2:c₁, …) = P⊗P₀₁ · bA · P⊗P₀₁`; after the same
  reductions, `A`'s rotations become `P⊗P r P⊗P` (local), `A`'s remainder
  `P⊗P · boxN · P⊗P` (idle on `3`).  The pairs: rotations, semantic; `A`-rem
  against `B`-rem by `BoxPPBridge.commBBpp` (after `X` on wire `2` and the
  swap of the wires `0, 1`); `A`-rot against `B`-rem by (322)/(323)
  (`E337.commR_ppB`); `A`-rem against `M q M'`: conjugate by `P⊗P`, then `gcl`
  with the word `ppL ++ RW q ++ ppL`.  (342): same, with `B = hg[0,2]`.

**What is left after that.**  (333), (334), (346)–(352), and the widths
`N = 4, 5` of (339), (342), (344).  (333) from (339): by Definition 2.4
`ZX = CH · B · CH · B` with `B` the box on wire `1` (all black), so (333) is
`Comm (HG · CH) B` (`HG` the multi-controlled `H` with box wire `2`, `H` on
wire `0`; both involutions).  Write `H_k` for `HG` with its controls on the
wires `3, …, k` black and the wires above idle (`H_2` is `CH` up to a
semantic step).  Then `CH · HG = (H_2 H_3)(H_3 H_4)…`, `H_k H_{k+1}` is, by
(310), `HG` white on wire `k + 1` and idle above; merged over the idle wires
it is a product of fully coloured `HG`s, each separated from `B` on wire
`k + 1`, so each passes `B` by (339) (relabelled by the 3-cycle
`0 → 2 → 1 → 0`, `swBH`).  This is the paper's argument (page 233);
`MergeAll.mergeListB0`, `isolate_black` are the box versions of the merges.
(334) from (333) and Lemma B.5 ((311), (312), (317)).  (346)–(352) per the
paper from (333)/(334) and (335)–(345), except (346), (351) with `x = y`
((351): trivial for `a = b`, (317) and `Comm.inv` otherwise; (346): the
paper's six-step chain).  At three wires the decomposition of (333) does not
separate the factors (the hole of its multi-controlled `H` is the only bulk
wire), so the three-wire cases of (346)–(352) need their own derivations.

**Do not import `D/N15*` in `N13`**: `N15/E353c`, `E354` use `D.eq333`,
`D.eq339`, so (353) (`Sym353`) is unavailable.  Rotations can be relabelled
on controls `≥ 2` through Definition 2.4 (`CH B CH B`) and (307).

**Small widths.**  At `N = 5` every frame tried leaves a pair of pieces
covering all five wires that is not (267)/(268); at `N = 4` the paper's
chain uses (295)₄ (`N8.eq295`, open, other package), (319)₄, (326)₄,
(327)₄.

**Builds.**  `check.sh` kills a build after 3600 s, and other packages' runs
hold its lock for long stretches; a cold build of the `N13` closure also
needs `W5/Family267`, `Family268` (about half an hour each).  Never `pkill`
by a pattern that occurs in your own command line (it kills the shell).

### Package (v), third session (2026-10-29): memory, (337), (338), and a plan for (339)

**Memory, measured.** A watchdog logging each `lean` process's anonymous RSS
(`/proc/<pid>/status`, `RssAnon`; `gen/sec8/n13/watch.sh`, run in WSL with
`setsid nohup … &`, kills a package-(v) build above 4.5 GB) shows: the imports of the N13 closure map
about 2.8 GB of `.olean` pages (file-backed, shared between processes, not a
risk); on top of that one engine semantic window of 22 letters on four wires
costs about 0.7 GB in the kernel (4 s), and the kernel frees it only at the
end of the declaration.  With the default `Elab.async` several declarations
are also checked in parallel.  So: **one decided run per declaration and
`set_option Elab.async false`**.  `E322` now takes 127 s and 0.9 GB (was 11
GB; generator `gen/sec8/n13/split_e322.py`); `E337r1`, `E337r2` 140 s and 1.0
GB each (`gen/sec8/n13/split_rr.py`); `W4/BoxHgLow` 0.7 GB (was over 4.5 GB:
118 decided runs in parallel).  A five-wire window is out of reach: one
`SE.lcheck 5` of two 34-letter words passed 4.5 GB in 20 s, so the drafted
route of (339) (`E339r3`, `chkTBR`) cannot be built.

**(337), (338): done** (`N13.eq337`, `eq338`; commit 2f7ebcdb).

**`N13/SepSem.lean` (builds, nothing imports it yet): semantic facts without
simulation.**  `Triv p v U`: `U` is the identity on the states whose wire `p`
is `v`; `Triv.comm`: two operators trivial on complementary blocks commute;
`Triv.conj` with `Route` (a circuit carrying wire `p` to `q`); `triv_lamOp`,
`triv_g` (a multi-controlled letter is trivial where a local control does not
match), `rtW`/`route_wc` (following a wire through a word of engine letters:
swaps move it, other letters must avoid it), `triv_conj`, and `sep_sem`:
`S.sem M (wc K M (u ++ w)) = S.sem M (wc K M (w ++ u))` for words trivial on
complementary blocks of one wire.  Any separated pair (opposite colours on a
common control) that shares an idle wire is then a semantic step with no
kernel simulation (`Frame.window` with `hsem` from `sep_sem`, or `semIdle`),
whatever its length and width.

**(339) from six wires on, the plan (numerically checked,
``gen/sec8/n13/f339.py`).**  Frame of `E339a` (sep_reduce at wire 3,
then the swap of the wires 2, 3): `A` = box[0] (1: c₂, 2: ●, 3: c₁, bulk x),
`B = BE` = hg[1,3] (0: c₃, 2: ○, bulk y).  The predecessor's `expBE` writes
`B = M · box[0](colOn 1 (yS c₃ y)) · M'`, whose separator is the box's wire 1;
relabel by the swap of the wires 1, 2 (`box_relabel`, j = 1) so the box is
`G` = box[0] (1: c₃, 2: ○, 3: ●, bulk y): then every piece of `G`'s
expansion (`expX`) is white on wire 2, and `M S₁` carries wire 2 to wire 2
(`rtW`), so each conjugated piece is `Triv 2 1`.  Expand `A` with the triple
`1, 2, 4` (relabel `S₃`, `box_relabel` j = 3): its rotations live on
`{0, 1, 2, 4}` (idle on 3), its remainder `Ar` = box[0] (1: c₂, 2: ●, 3: c₁,
bulk ≥ 5) is idle on 4.  The four kinds of pairs:
  * rotation vs conjugated rotation: all local on the wires 0–4: `sep_sem` at
    width 5, completeness on five wires (`ih 5`, needs N ≥ 6) and `der_loc`;
  * rotation vs conjugated remainder (`remB`: `swAt 0 · boxN y c₃ false ·
    swAt 0`, the box on wire 1 idle on 3): `sep_sem` without wire 3;
  * `Ar` vs conjugated rotation (local on 0–3): `sep_sem` without wire 4;
  * `Ar` vs conjugated remainder: two boxes (box wire 0 with control 1, box
    wire 1 with control 0), idle on 4, resp. 3: split each idle wire by the
    merge (309) and use `eq336` (proved at every width).
**Status of that plan.**  `E339a` builds now (71 s, 2.4 GB anonymous:
`chkMM` split, `base_circ` repaired, more heartbeats for `expBE`).
`N13/E339s.lean` (builds, 24 s, 1.5 GB; nothing imports it) has the word
`uL … uL'` (`M` then `S₁`; `rt_uL`, `rt_uL'`: it carries wire 2 to wire 2),
its inverse at every width (`uL_inv`, `uL_inv4`, from `inv_of_lcheck`: a
four-wire decision lifted through `eval_wc_blk`), `triv_rots`, and two of
the four kinds of pairs: `commRR_s` (`[S₃, r, S₃]` against
`uL ++ [h] ++ uL'`, on five wires) and `commAr_s` (`Ar` against
`uL ++ [h] ++ uL'`, without wire 4).  Still to do for N ≥ 6:
  1. `A ≈ drawn` of its pieces: `box_relabel` with j = 3 (wires 3, 4 both
     controls), `expX` on the relabeled colouring (1: c₂, 2: true,
     3: x 4, 4: c₁), `conj_drawn` with `swsw _ 3`; the rotation pieces are
     `[S₃, r, S₃]` (as in `commRR_s`); the remainder `S₃ · boxN · S₃` is
     `Ar` (coloured by `x` above 4) by `mc_swap` (wire 3 idle there, so no
     `CanonSym` needed), or keep it as `[S₃, P3', S₃]` and drop wire 4 after
     `mc_swap`.
  2. `B ≈ drawn` of `(uL ++ [g] ++ uL')` over `pcs4 c₃ false true`: `expBE`,
     `box_relabel` with j = 1, `expX`, `conj_drawn` (inverse `uL_inv`
     turned into derivations by `MM_inv` and `swsw`, or by completeness).
  3. Pair rotation vs remainder of `B`: `remB` (after the S₁ relabel of the
     remainder) makes it `swAt 0 · boxN y c₃ false · swAt 0`, the box on
     wire 1 idle on 3; the rotation of `A` must first be made a single
     letter on `{0, 1, 2, 4}` (`mc_swap` of `[S₃, r, S₃]`), then `sep_sem`
     without wire 3 exactly as `commAr_s`.
  4. Pair `Ar` vs remainder of `B` (box[1] (0: c₃, 2: ○, bulk ≥ 4), idle
     on 3): merge each idle wire ((309): `Ar` = `Ar(4 ●) Ar(4 ○)`, the other
     on wire 3) and apply `eq336` (proved at every width) to the four
     products.
  5. Assemble with `comm_drawn`, colour the bulk (`colour_wc` as in `gcl`),
     and reuse `E339.comm339_core`/`comm339_ge6` (the frame and
     `sep_reduce`), replacing `comm339E`.  `E339.lean`, `E339r1`–`r3` are
     the predecessor's infeasible route and can be deleted then.

**Widths 4, 5 of (339).**  At N = 5 every frame leaves one pair covering all
five wires.  With `G`'s triple `3, 2, 1` instead, the pair "remainder of `A`
vs conjugated rotation of `G`" becomes (322) by the relabeling 1 → 0, 3 → 1,
0 → 3 and (274) (`commB_ppRw`), but then "rotation of `A` with target 0 vs
`hg[1,3](2: ○, bulk)` idle on 0" is left; the paper's own chain (pages
216–219: (244), (308), (214), (319), (215), (243), (111)) is the way there.

### Package (v), fourth session (2026-10-29): (339), (342), (344) from six wires; (333), (334), (346)

All built and committed (commits fcd0554e, d653953f, 78200cc9, f1e411a9); no
file decides a semantic window; peaks 0.27–0.49 GB anonymous (watchdog
`gen/sec8/n13/watch.sh` running in WSL).

* `N13/E339b`: (339) from six wires on (`comm339_ge6`), steps 1–5 of the
  third-session plan.  The predecessor's infeasible `E339`, `E339r1`–`r3`
  are deleted (`E339a`, `E339s`, `Loc5` stay: `E339b` uses them).
* `N13/E344s`, `E344t`: (342), (344) from six wires on (`comm342_ge6`,
  `comm344_ge6`).  In (339)'s frame the first gate is `P ⊗ P` around
  (339)'s box with `c₂` black (`hg0_box4`); conjugating the pair by `P ⊗ P`,
  the second gate's pieces are `E339b`'s conjugated by a word `Q` on the
  wires `0, 1` (`QOK`; `P ⊗ P` for (344), `P ⊗ P` and `S₀` for (342), since
  (342)'s second gate is `BE` under `S₀`).  The pairs are generic in `Q`;
  the two remainders, merged on their idle wires (309), are (338) under
  `S₀` for (344) and (337) for (342).
* `N13/E333`: (333) given (339) at the same width (`comm333`), and (334)
  (`comm334`, from (333), (317), (311), (312)) — the paper's page-233 merge.
  Reusable there: `mergeHg0`/`mergeListH0` ((310) with idle wires and over a
  list of wires: a copy of `E/MergeHg`, which cannot be imported since
  `E/Transport` imports `D/N15`), `hgR` (`S₁ (S₀ · S₀) S₁` carries
  `hg[0, 1]` to `hg[2, 0]`), `hg_ch` (`CH` is `hg[2, 0]` with its only
  control on wire `1`, by two swaps and (f4), at every width from three and
  without completeness), `HGc_B` ((339) under the 3-cycle `0 → 1 → 2 → 0`).
* `N13/E346`: (346) at every width from three (`comm346`): by (81) on both
  gates (`MergeAll.colour_ind`) the rotation is black, (333)/(334) write it
  as `HG333`, `B333`, and the box passes those by (338) under `S₁` and by
  (336).  The paper's chain holds for every `x`, `y`, not only `x = y`.
* `N13.lean`: `eq333`, `eq334`, `eq346` wired (they use `eq339`, which is
  moved above them); `eq339`, `eq342`, `eq344` dispatch on the width: one
  marked `sorry` branch for `N ≤ 5` each (the other agent's `N13/Low339*`,
  `Low342*`, `Low344*`; replace the branch when those build), `6 ≤ N` from
  `E339b`, `E344t`.

**Left in package (v)**: `eq347`–`eq352`, and the width-4/5 branches.

**Plan for (347)–(352)** (not started).  The paper (page 234): with (81),
(315), (316), (333) and (334) write any coloured rotation as boxes and
multi-controlled `H` "with a hole", and (335)–(345) apply "whenever there
is a black control in front of a white one"; for (351) with `x = y` it is
trivial (`a = b`) or (317).  Two ingredients are missing:
1. Colour reduction as in `E346` (on both gates by (81); a control of one
   gate on the other's box wire is absorbed by (315)/(316)), then the
   decomposition of the black rotation (`HG333`, `B333`).
2. The decomposition with the `H` gate's box wire on any wire `j ≥ 2`, not
   only `2`.  It is needed: e.g. (347) reduces to `box[1](0: c₁, 2…: x)`
   against the black `ZX`; the pieces are (335) under `S₀` and (339) under
   the 3-cycle (as `HGc_B`), which needs `x` non-black on a wire `≥ 3`; if
   `x` is non-black only on wire `2`, `HG333`'s box wire is `2` and that
   pair is not separated (it does not commute).  The black rotation is
   symmetric in its controls: for the swap of wires `j, j+1`, `j ≥ 3`, both
   pieces pass it by `swBH`; for `j = 2` (and `1`) this is (353) at the
   canonical position, whose paper proof (page 235) uses only (307), (310)
   and (339), all available here (`D/N15/E353c` itself cannot be imported).
   Prove `ZX ≈ drawn [hg[j,0](1, others black), B333, …]` for `j = 3`, and
   choose the decomposition so that the separating wire is a control of
   both pieces.
Then: (348), (349) (`hg[0, 1]` against a rotation on wire `0`, resp. `1`):
pieces against `HG` by (340)/(344)/(345) relabelled, against `B` by
(337)/(338) relabelled; (350) is target `2`; (351) `x ≠ y` and (352) reduce
to (347)-type pairs.  Three wires: the decomposition has no wire `≥ 3`, so
check numerically which three-wire instances are not covered by
(335)–(345) at `N = 3` and derive those separately.

**Pitfalls met.**  `rcases … with rfl | …` inside a `macro` does not
substitute (the pattern `rfl` gets macro scopes and becomes a variable):
use `with h | h … <;> (try subst h)` (`ctl_case9`, `ctl_case33`).  The old
`ctl_case` of `E339a` only works through its `simp_all` fallback, which
times out when the context holds large `Derivable` hypotheses — prove
control equalities in small lemmas.  `swBH`'s control functions cannot be
left as `_` in a `have` (nothing determines them).  `dropW` is ambiguous
between `Net` and `SE` when both are open.

### Package (vi), fourth session (`rcch-e`, 2026-10-29): Lemma 8.5, rules (36), (37)

Proved and wired (commits 55d00de7, 9b8cdce1, ee0eb1be); every step checked
numerically first (`gen/sec8/e/m85.py`: 2008 cases at `n = 3, 4, 5`;
`gen/sec8/e/m36.py`: the decoded swaps, negations and both rules at `n = 3, 4`, 143 cases).
`lemma_8_8` is now open only at **(45), (46)**.

* **Lemma 8.5 at every width**, `E/Lemma85.lean` (`lemma85`): for a state `s`
  with bit `t` clear, `D((-1)_[G⁻¹(s)]X_[G⁻¹(s),G⁻¹(s⊕2^t)])` is
  `mc .xz [t] (ctlOf s t)` and the sign on `G⁻¹(s⊕2^t)` gives `.zx`.
  Induction along `dZXab` two levels at a time (`lemma85_of`; the five letters
  are the paper's five factors); the step `Step85` at the canonical position
  (`t = 0` the inner letter, `β = 1` the outer ones, wires above white,
  `step85w`) is the paper's chain read algebraically in the quotient monoid
  (`alg85`): the first two letters are `Mκ` ((354)), the last two its inverse
  ((317) on full controls, `rot_inv`), the single-qubit `(-1)ᵏ XZ` on wire `1`
  is `Mκ R` by (354) over every colouring of the other wires (`U85_split`,
  `mergeListGen`), every factor of `R` passes the result by (352), and (359)
  recolours the control.  Other colours above by (81) (`step85c`, `colr85`),
  any two wires by the frame of `[t, β]` (`frame2_one`).  General tools there:
  `comm_prod_left`, `conj_back`, `kind85`/`kindZX_eq`, `dist_odd`.
* **Decoded swap and negation**, `E/Swap36.lean`: `dec_encSwap` (`D(E_{k,ℓ}(swap))`
  is `swAt ℓ`) and `dec_encNeg` (`D(ℰ⁰_{k,ℓ}(X))` is `xAt ℓ`): the decoded `CZ`/`Z`
  (`lemma86_CZ_*`, `lemma86_Z_*`), the products of mixed letters by Lemma 8.5
  and (354) (`decode_zx_list`, the zx analogue of `decode_zz_list`), and a
  two-wire (one-wire) identity by Lemma 5.1 through `placeG_mul2`,
  `placeG_der2`, `placeG_swap`.
* **Rules (36), (37)**, `E/Rule3637.lean` (`dec36`, `dec37`): the left side by
  `dec_patt` (from `patt = some (k, u, w)` alone, `patt_bounds`); the right side
  `wW` cut into blocks (`wW_eq`), the swaps decoded to `swW` of the network
  `netW kind w (u - w - 1)` (`dec_net`), the negations to `X` gates
  (`dec_neg`, `xOpt`, `prod_map_ite`) that colour the gadget by `recolour`,
  and `placedBy_mc`; `pos_netW_zero/one/ge` say where the network carries
  each wire, which is Definition 8.3's placement.

**(45), what I found (no Lean yet).**  Decoded, (45) is (146) with every wire
`≥ 3` a white control (`m45.py`): `E1 = hg[2,0](1○, C○)`, `E2 = hg[0,1](2○, C○)`,
`Bw = box[0](1○, 2○, C○)`, `C` the wires `3, …`; as the letters are
involutions it says `Bw` inverts `(E2 E1)²` (operator order).  Two shortcuts
fail, for reasons worth not rediscovering:
* merging over the colours of a wire `q ∈ C` only gives
  `K(q idle) = K○ K●` with `K○`, `K●` commuting and `X_q`-conjugate, and
  Lemma 5.1 gives `K(q idle)² = 1`; that is `J (X J X) = 1` for `J = K●²`,
  which does not force `J = 1` (same with several wires);
* no conjugation can turn the `C`-controlled gates into gates idle on a wire
  (the multiplicities of their eigenvalues differ), and a multi-controlled
  `H` with `N - 2` controls has no free wire for its box, so `E1` cannot be
  split over the colour of wire `2`.
So a real derivation with the controls `C` is needed.  The paper's (pages
264–269) starts by inserting `box[0](1○, 2●)` twice ((311)) so that it
merges with `Bw` ((309), wire `2` idle), and pairs `hg[0,1](2○, 3●)` ((312))
so that the `H` gates merge over the auxiliary wire `3` ((310)), which then
frees wire `3` as a box wire ((277), (274)); then `P ⊗ P` frames ((112),
(246), (111), (130), (308)) and (307), (313), (336)–(339), (335) to a
symmetric form (II); the right side reaches the mirror image.  About 25
diagrams; `gen/sec8/figparse.py` reads page 264 partly (it misses the box
wires drawn as dotted squares and the dashed ellipsis), so the chain must be
transcribed by hand from the rendered pages (render at 200 dpi in halves;
the wires bottom-up are `0, 1, 2, 3, 4`, the dashed segment the wires `5, …`).
**(46)** is (147) with white controls, eight pages (269–277).

`E/Rule45.lean` (commit 3e17ea84) states the decoded rule as `Core45 M`
(`E1h45`, `E2h45`, `Bw45`, monoid order) and proves `dec45_of : Core45 M →`
the case (45); `lemma_8_8`'s case `r45` is `E.dec45_of sorry`.  At `M = 0`
`Core45` is (146) itself (`Small.eq146 0`), after rewriting the three gates
by `placeG_shift_cons` (their box wire is idle on three wires: `mch 1 =
shift ch`, `box 2 = shift cz`) — not done.  The decoded letters of (46),
computed the same way (`dec_patt`): `H_[3,4]H_[2,5]` is `hg[0,2]` and
`H_[3,2]H_[4,5]` is `hg[2,0]`, both black on `1`; `H_[7,6]H_[4,5]` is `hg[1,0]`
(black on `2`), `(-1)_[2](-1)_[3]` the box on wire `0` black on `1`, white on
`2`; every wire above `2` white.

### Package (v), fifth session (2026-10-29): (347)–(352)

Built and committed (all in `Sec8/D/N13/`, namespace `N13.R347`; no decided
window anywhere, each module well under a minute):

* `S353`: (353) for the black canonical rotation at every width, the
  argument of `D/N15/E353*` with (333), (339), (317) as hypotheses
  (`H333`, `H339`, `H317`); `sym353`, and `mcSwapAll : E.McSwapAll N`, so
  rotations move along swap networks too.  `N13.lean` has
  `D.mcSwapAll N ih` from `eq333`, `eq339`, `eq317` at every width `≤ N`.
* `RotDec`: `dec_at` — any rotation `(-1)ᵃZX` with target `t` and a control
  of any colour on every other wire is `HG B HG B` (`ZX`) / `B HG B HG`
  (`XZ`) with `HG = mc .hg [h, t] (setCtl c h none)`, `B = mc .box [b]
  (setCtl (setCtl c b none) t (some true))`, for any distinct `t, b, h`
  (canonical coloured version `dec_canon` from (333)/(334) by (81), with
  `x1_box` (315) and `x2_hg` (316) for the box wire and hole; then the frame
  `[t, b, h]`).  Also `comm_frame`, `frm_ctl`, `diff_frm`, `rd` (colours read
  through a frame), `x0_hole_hg` ((316) for coloured `hg[0,1]`).
* `Framed`: `f335 f336 f338 f339 f340 f344 f345` — (335)–(345) on any wires,
  control functions given pointwise by their values on the special wires and
  "a control elsewhere".
* `E347`: `comm347` (every `N ≥ 3`), `comm348`, `comm349`, `comm350`,
  `comm351`, `comm352` (`N ≥ 4`), `comm351_same` ((351) with equal
  colourings, (317)).  The choices of box wire/hole are in the module header;
  `gen/sec8/n13/r347.py` checks them (and `dec` the decomposition).
* `N13.lean`: `eq347`, `eq350` proved; `eq348`, `eq349`, `eq351` (different
  colourings), `eq352` have one marked `sorry` branch, `N = 3`.

**Three wires (open).**  The paper's argument (page 234) does not cover them
(README records the gap): with only the separating wire to spare, some pair
of factors never commutes (`r347.py` prints the uncovered cases).  Reductions
found (not yet in Lean):
* (349)₃ ⟸ (341)₃ + (337)₃: `dec_at` with `t = 1, b = 0, h = 2`; the box
  `box[0](1:●, 2:y)` against `hg[0,1](2:x)` is (337), the `H` gate
  `hg[2,1](0:c₁)` against it is (341) at three wires (same `H` wire, each hole
  the other's control, every colour), which is D.2's (135) (`W3T.td135`:
  `[S0, K1, S0]` is `mc 3 .hg [1,0] (ctlAt 2 true)`, `K0` is `hg[2,0](1:●)` by
  `E333.hg_ch3`) under the swap of the wires 0, 1, coloured by `X₀`
  (`x0_hole_hg`, (81)) and `X₂` ((81), and (316) for `hg[2,1]` = `x2_hg`
  conjugated by `S₀`).
* (351)₃: colourings differing on one wire are (136)+(137) (`drawn [R(●,○),
  R(●,●)]` and `drawn [R(●,●), R(●,○)]` are both `ZX(1:●)`), with (81) on both
  wires, the swap of the wires 1, 2 (`comm_zx_sw_3`) and (317) for the signs;
  on both wires: decompose the black one with `b = 1, h = 2`, then (347)₃ and
  (349)₃ moved by a frame (rotations move with `mcSwapAll 3`).
* (352)₃: half-dots black is (139)/(140); `c₁ = ○`: decompose the second
  rotation with `t = 1, b = 2, h = 0`: its `H` gate `hg[0,1](2:y)` against
  the first is (348)₃, its box `box[2](0:c₂,1:●)` against the first is (347)₃
  moved by the frame `[2, 0, 1]` (separated on wire 1); `c₂ = ○` by the swap
  of the wires 0, 1.
* (348)₃ itself has no reduction: neither decomposition of the rotation
  works, and (139)/(140) (with `CZ(0,1)` turning the rotation over) do not
  imply it algebraically.  It needs a three-wire derivation like the paper's
  proof of (139) (page 70: (14), (9), (81), (132), (111), (112), (18), (114),
  (17)).  The w4 solver (`gen/sec8/w4/proj.py`) fails at once on these
  instances (`core`: `letters_util.decompose` only knows four-wire gadgets).

### Package (v), small widths of (339), (342), (344) (2026-10-29)

**Done: `eq339`, `eq342`, `eq344` in `N13.lean` hold at every width** (the
N ≥ 6 branch is the other session's `comm3xx_ge6`).

* `N13/Low339.lean` (`L339.comm339_ge5`, `eq339_5`), `Low344.lean`
  (`L344.comm344_ge5`, `eq344_5`), `Low342.lean` (`L342.comm342_ge5`,
  `eq342_5`): the three equations from five wires on, at every width, in
  the paper's frame.  No kernel simulation except two three-wire `Fast`
  checks; under a minute each, peak 0.7 GB anonymous.
* The pair the earlier sessions found blocking at `N = 5` (a remainder idle
  on the `H` wire of `B` against a rotation of `B` conjugated by `P ⊗ P`,
  covering all five wires) is the paper's (326)/(327), and is cheap: `P ⊗ P`
  is a tensor product of one-qubit gates exchanging `Z` and `H`, so on three
  wires `P₀₂ = P₀₁ P₁₂` (`L339.klein1`, `klein2`, decided by `Fast` on three
  wires), and `P ⊗ P` on a box wire and an idle wire passes the box ((276),
  `L339.pp276`, from `N8.s276`).  Hence `P₁₂ R P₁₂ = P₀₁ R P₀₁` for the
  remainder `R` (idle on wire `2`), and the pair is (322)/(323)
  (`E337.commB_ppRw`, `commR_ppB`, `E322x.eq322_word`), which hold from five
  wires on.  The other pairs: rotations by `SepSem` (a semantic step without
  wire `4`, no simulation), rotation against remainder by (318)/(319)
  (`E336x.commRBs`, `commBRs`) or (322)/(323), remainders by `commBBs` or
  `BoxPPBridge.commBBpp`.  Every identity was checked numerically first.
* Frames: (339) `A = S₂ · Abox · S₂`, `B = U · Bbox · U'` with
  `U = S₀ S₁ (P ⊗ P) S₁ S₂`; (344) `A = (P S₂) · Abox · (S₂ P)`, `B` as in
  (339); (342) `A` as in (344), `B = W · Bbox · W'` with `W = S₁ (P ⊗ P) S₁ S₂`.
  `Abox`, `Bbox` are the boxes of `E336x` (expansion `expX`); both remainders
  are idle on the `H` wire of `B`.
* `N13/Low339W4.lean`, `Low344W4.lean`, `Low342W4.lean` (`L3xxW4.eq3xx_4`):
  generated by `gen/sec8/n13/low4.py 339|342|344` (the W4 solver, every W4
  module loaded as known equations with qualified proofs).  All black: D.3's
  (184), (205) relabeled, (203) relabeled.  A white control on the `H` wire
  of the other gate is merged away ((170a)/(166), (171a)/(167) and its flip
  on wire `3`); the merged gate is a two-wire gate with a dummy box wire
  (a semantic step on three wires), which passes the other gate through
  Definition 2.4 and (155)/(163), (154)/(159), (164).  Other colours by
  `derive_flip`.  Each builds in under a minute, peak 1.6 GB.
* Solver notes (`low4.py`): an `H` on one wire must be the placed token
  `tp 1 [H 0] [q]` for a relabeled table entry to match; a `CH` must be spelt
  exactly as the derived flip spells it (`164f2`: `X X K X X`), the respelling
  done by a semantic step; a two-wire gate past `P ⊗ P` on the other two wires
  goes fast with both as letters (`sw`), while `P ⊗ P` on the wires `0, 2`
  (interleaved) did not finish in 15 minutes; conjugation by one swap is done
  by `conj_step` (`Solver.conj_down`), which the search does not find alone.

**Update (same session, later).**  Three wires done except (348):
`N13/E347t` ((341) on three wires `c341`, from D.2's (135) `c135`; (349) on
three wires `comm349_3`), `N13/E351t` ((351) on three wires `comm351_3`),
`N13/E352t` ((352) on three wires `comm352_3`, given (348) on three wires as
the hypothesis `H348 3`).  In `N13.lean`, `eq349`, `eq351` are proved at
every width and `eq352` has no `sorry` of its own; `#print axioms` gives only
`propext`, `Classical.choice`, `Quot.sound` for `eq347`, `eq349`, `eq350`,
`eq351`, and `sorryAx` for `eq352` through `eq348`.  The only open branch of
(347)–(352) is `eq348` at `N = 3`: `hg[0,1](2:x₂)` against
`(-1)ᵃZX[0](1:c₁, 2:y₂)`, `x₂ ≠ y₂` (after (81) on wire 2 and (317): two
instances, `c₁ = ●, ○`).  What is known about it: no decomposition of the
rotation into boxes and `H` gates has all pairs commuting
(`scratchpad`-style check: on three wires the `H` gate `hg[2,0](1:c₁)` of
the `b = 1, h = 2` decomposition and the box `box[2](0:●,1:c₁)` of the
`b = 2, h = 1` one never commute with `O`); `O` is `P⊗P · box[0](1:●,2:x₂) ·
P⊗P` semantically, but `P⊗P R P⊗P` is no multi-controlled gate; and every
three-wire relation available for `R` with `O`'s neighbours ((139), (140),
(345), (338), the turnover by `CZ(0,1)`) keeps the wire 1 monomial, so `H₁`
is never reached — a derivation must use a relation with `H` on a control of
the rotation, as the paper's proof of (139) (page 70) uses (114), (18),
(111), (112), (132).

### Package (vi), fifth session (`rcch-e`, 2026-10-29): rule (45)

Proved and wired (commits 17af109f, acac8323): `lemma_8_8`'s case `r45` is
`E.dec45_of (E.core45 M ih')`; Lemma 8.8 is open only at **(46)**.  Every
fact was checked numerically on the circuits at `N = 4, 5, 6`
(`gen/sec8/e/m45b.py`; the paper's chain itself, transcribed from the PDF's
vector data, is valid diagram by diagram at `N = 6, 7`).

* **Width 3** (`E/Core45.core45_zero`): (146) (`D.eq146`) with the gates
  rewritten by `placeG_shift_cons` (their box wire is idle).
* **Width ≥ 4** (`E/Core45.core45_pos`): not the paper's diagram-by-diagram
  chain but its content regrouped as one identity of the quotient monoid
  (`E/Core45Alg.alg45`, abstract, 14 involutions, 37 facts, 13 box
  commutations).  With `T = a b a w b` (monoid order, `a = E1`, `b = E2`,
  `w = Bw`), every letter an involution, the rule is `T T = 1`:
  - `T = k V`, `V = a e a v e`, `k = B[0](1○2●3○)`: `w = k v` ((309)),
    `b = f e` with `f = H[0,1](2○3●)` ((310)), `f` passes `a` ((344)), `w`,
    `k` ((337)), `b` ((340)); `k` passes `a` ((338)), `b`, `f` ((337)), `w`.
  - `V = P₀₁ X P₀₁`, `X = q h₁ z₀ h₀ z₀ p`: Definition 2.4 for `b`, `f`
    (frame `[0,1]`), `a` (`[2,0]`), `h₀`, `h₁` (`[2,1]`); Klein (130);
    (308) for `v`, `p`, `q`; merges (309) and box moves (274).
  - `X X = 1`: `h₁` passes `z₀` ((339)) and `h₀` ((340)); `p`, `q` pass
    `h₀`, `h₁`, `z₀` (boxes commute, (308)).
  The paper's (246), (111), (313), (335)–(338) chain steps are not needed in
  this form; the frame `[0,1]` for `e` replaces the paper's `[3,1]`.
* **Tools** (`E/Core45Kit`): `ctlF s l` (special/idle wires `l`, colours the
  bits of `s`), `frameFI`/`frameF` (a canonical gate coloured through a frame
  is the framed gate, for any colours), `commF` and its instances
  `comm337F`, `comm338F`, `comm339F`, `comm340F`, `comm344F`, `hgInvF`,
  `hgFrameF` (coloured Definition 2.4 at any wires, from `N13.hg_box`),
  `c308`/`c308F` (coloured (308)), `move274F`, `ppSymm12`.  In
  `E/Core45Facts`: `ctlF16` (compare colourings on the local wires),
  `setCtl_someF`/`setCtl_noneF`, `m45box` ((309) in `ctlF` form).  These
  apply to any statement whose gates have full colourings on a few local
  wires, which may help (46).
* Dependencies: `eq339`, `eq344` at four wires (open in `N13.lean`, other
  agents).  Builds: each file under a minute.
* Pitfalls met: `rw` with a `setCtl_someF` whose `b` is left to `by decide`
  matches the wrong factor — give `(b := …)`; facts touching wire `3` need
  `1 ≤ M`; `show … from rfl` for `place2 2 0 ch = Circuit.pad 0 ch` failed in
  this file (use `congrArg shift (pad_zero2 ch)`).
