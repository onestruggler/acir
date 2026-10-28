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
* `figparse.py` — **prototype** of the figure parser (PyMuPDF): `page_items` collects the
  vector items of a page (horizontal/vertical segments, filled and white dots, boxes,
  dashed boxes, curves, text spans); `merge_wires` joins wire fragments split by
  boxes (not across an `=` sign); `diagrams` groups wires into diagrams by the `=`
  sign they flank (nearest in height).  State: on the D.2 statement pages most
  diagrams come out right, but some are mis-split (page 67 gives 2- and 4-wire groups
  where all are 3-wire), and on proof pages the `=` signs carrying citations are
  missed (they are not separate text spans).  Still to do: those two fixes, gate
  extraction per diagram (connected components of dots/boxes along vertical
  segments; swaps from curves; `P ⊗ P` from dashed vertical links), and output as
  `Eng.L` letter words checked numerically with `mc.py`.
