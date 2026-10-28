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
