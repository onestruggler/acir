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
| Clément [2026], real Clifford+CH | Theorem 4.10 item (a) proved, item (b) open; Lemma 8.8 and the Appendix D interfaces partly proved (uncommitted) |

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

* Item (a): proved, `Sec8/A/ItemAProof.lean` (`item_a_proof`), wired in
  `Thm410Proof.lean`.
* Frame machinery, all building: `Sec8/A/FrameSteps` (push lemmas), `FrameFS` (A.5
  tails at numerals, τ words on ℕ), `FrameCases` (every coset and generator),
  `FrameRun` (`Tc`, `fs_all`, `frame_run`, parity of `hstar`, `good_frame`: a relation
  holds when Figure 8 derives its frame images).
* Item (b), the plan:
  1. Every relation of Figure 6 on at most four indices except (d3), through
     `good_frame` and `ItemBPhi`'s `img_*`.
  2. Then pull the `Good` congruence back, use completeness of Figure 6 on `k`
     indices, and a renaming principle (elementary moves via (c1)–(c5), (b2),
     (b3), (b5)).
  3. A chain checker at `Fin m` whose steps are semantic.
  4. (d3*) and (46) directly, at positions avoiding 0 and 1. Chains are designed
     in Python: (d3) in 83 steps with semantic steps on three indices, (d4) in 67
     steps with semantic steps on five (`.handover-scratch/thm410/d3chain.py`,
     `d4chain.py`).
* `ItemASteps.lean`/`ItemBFun.lean` from the earlier commit did not build at the
  start of the session; check whether they are still needed.

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

`CliffordCS3/Completeness.lean` (rsData) · `RealCliffordCH/Sec8/Thm410Proof.lean` 1 (item (b)) ·
`Sec8/Lemma88Proof.lean` 8 · `Sec8/D/N13.lean` 19 · `Sec8/D/N15.lean` 3 · `Sec8/D/N8.lean` 1 ·
`Sec8/D/W3.lean` 6 · `Sec8/D/W4.lean` 5 · `Sec8/D/W5.lean` 3.
