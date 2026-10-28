# Section 8 scripts (Python 3 + numpy)

* `mc.py` — a model of `Syntax.lean` and `Sec8/MC.lean`: circuits as gate lists in
  drawn order, their matrices, the canonical multi-controlled gates, `netL`, `placeG`,
  `colourW`, `mc`; `python mc.py` checks `mc` against its intended semantics
  (`Λ_c(U)`) on random placements (500 cases, widths 2–6).
* `iface.py` — the interface statements of `Sec8/D/N8.lean` and `Sec8/D/N13.lean`,
  checked numerically at widths 3–6 (`python iface.py [eq ...]`).
* `cites.py PAPER.txt FROM TO` — for each "Proof of Equation (N)" in the PDF text of
  arXiv:2602.06644, the equations it cites with their width subscripts;
  `closure.py` the equations transitively needed by Appendix E; `steps.py` counts
  derivation steps (`=` signs) per proof.
* `figparse.py` — the figure parser (PyMuPDF).  The figures are vector graphics:
  `page_items` collects wires (horizontal lines, also straight Bezier segments),
  vertical links (solid; dashed for `P ⊗ P`), black/white dots, circled pluses (`X`),
  white circles with a label (a control of parametric colour, e.g. `β`), labelled boxes
  (`H`, `ZX`, `XZ`, `P`, `(-1)^a ZX`), small dashed squares (the box wire of a
  multi-controlled gate) and swap curves; `wire_runs` joins wire pieces across swaps
  and labelled circles; `diagrams` finds, next to each `=` sign, the block of equally
  spaced wires of one x-extent centred near the sign's axis (never past half-way to
  the `=` signs above and below in its column), so stacked equations of equal width
  are not merged; `gates` links the items of a diagram along vertical lines and
  `classify` reads each component as a gate (`Z`, `Zw`, `H`, `X`, `SW`, `PP`, `CZ`,
  `BOX`, `CU` (multi-controlled `H`/`ZX`/`XZ`/`X`), `CHB` (multi-controlled `H` with
  its box wire)); `parse_page` returns rows of diagrams, `=` signs with the citations
  printed above them (`(81)(5)`, `Lemma 7.6`), and equation labels.
  `python figparse.py PAPER.pdf PAGE …` prints them.
* `model.py` — parsed gates as `mc.py` circuits (`circ`, the conventions of
  `MC.lean`) and as engine letters (`word`); `equal` compares two diagrams for every
  value of their parameters.  `letters.py` writes the canonical gates of Definition 2.4
  and the placements as `Eng.L` letters (`place`: shifted on increasing consecutive
  wires; a two-wire gate on wires `lo < hi` conjugated by `S lo, …, S (hi - 2)`, as
  `cz20`; upside down by the swap of its wires; otherwise `MC`'s network), mirroring
  the Lean definitions; every parsed statement's letters agree with `mc.py` (1125
  diagram instances).
* `checkpages.py PAPER.pdf PAGE …` checks that consecutive diagrams of each row are
  equal; `countpages.py` compares the `=` signs of a page with those placed in rows.
  State: on pages 66–87 and 136–138 every `=` sign is placed, and every row checks,
  except one step of the proof of (129) (page 69): its last diagram,
  `ΛZX(0|2,1)·CZ(2,1)·CZ(2,0)`, is a stray (it is not equal to the one before, which is
  already the right-hand side of (129)); on page 138 the statement (262) has a lone
  `P` box that the model does not read (not needed).
* `chains.py PAPER.pdf FIRST LAST OUT.json` — the statements (rows with a label) and,
  per `Proof of Equation (N)`, the derivation chains (rows continued by lines starting
  with `=`), each step checked numerically and each chain's ends against the
  statement.  For D.2 (pages 66–79): all 25 chains of (119)–(147) parse, 172 steps,
  every one numerically valid but the stray of (129); (117), (118) follow from Lemma
  B.2, (120), (122), (138) from Lemma B.3, (137) from (136) and (81).
* `gen_small.py D2.json D3.json D4.json OUTDIR` — writes `Sec8/D/SmallDefs.lean`,
  `Small.lean` and the stubs `W3`/`W4`/`W5.lean` from the parsed statements.  Letters
  are written qualified (`L.K 0`): dot notation (`.K 0`) under `++` made the
  elaboration of `SmallDefs` take over ten minutes.
* `eng3.py` — a model of `Sec8/EngineN.lean`'s steps (`apply_step` mirrors
  `Eng.applyStep`), reversal of runs, Lean output.  `w3.py D2.json [EQ …]` — turns the
  paper's D.2 chains into engine runs at width 3 (in progress): each step by local
  tactics (semantic windows on two wires, commutations, a letter passed across
  another by a two-letter semantic window, windows on wires 0, 2 conjugated by the
  swap `S 0`) and table rewrites with the cited equations (the three-wire rules
  (12)–(18), (f3), (f4), their mirror images, earlier D.2 equations).
