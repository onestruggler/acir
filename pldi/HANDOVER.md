# pldi/ handover, 12 November 2026

State of `pldi/qcert.tex` at the commit that adds this file, and what is
still open. Written for whoever continues on another machine: the session
notes, the mock review (`local/pldi-mock-review.md`, git-ignored) and the
scratch scripts stayed on the first machine.

## Done in the last round

* Title without "Quantum"; VyZX mentioned in the introduction; Figure 3
  uses T for the rule set; no "partial" marks in the status figure.
* The delta against the earlier library is measured against the branch
  `popl-submitted` (paragraph "Relation to the Earlier Library", Section 3).
* Fifteen published sources and one unpublished internship report
  (Clément 2019).
* The two Lean modules that did not build (`RealCliffordCH/Sec8/A/ItemBFun`,
  `ItemASteps`) are deleted (commit 99d329be).
* Table 1 has a Proof column (S, P, R, E; legend in the caption).
* Step (6) of Section 3.2 gives the size of what a reader must read
  (about 8,200 of 377,000 lines, 2%).
* Appendix B has a new subsection "Size and Provenance of the
  Formalizations" (`app:provenance`, `tab:provenance`): per row the code
  lines, generated, ported, statement lines, and the rows it uses.
  Every number comes from `pldi/compare/audit.py` (`audit.json`);
  run `python3 audit.py ../.. audit.json` in `pldi/compare`.
* Section 5 gives the split written / generated / ported
  (203,673 / 107,083 / 65,871).

## Open

1. **Lean time of the real Clifford+CH row (Table 1).** The row still
   shows 5478.79 s with a footnote about two helper modules that did not
   build. Those modules are deleted now. A re-timing was running on the
   first machine when the session stopped (about 1.5 h; it rewrites
   `pldi/compare/leantime.json` there, not pushed). To redo it anywhere:
   in WSL, in `pldi/compare`,
   `python3 leantime.py ../../Lean leantime.json RealCliffordCH`
   (nothing else heavy running), then
   * patch the Lean `RealCliffordCH` entry of `loc.json` (two files fewer:
     run `loc.py` to a temporary file and copy that entry),
   * `python3 figdata.py` and `python3 mkfig.py ../figures/compare.tex`,
   * update: the Table 1 cell and total, and delete the `*` footnote in its
     caption; Section 5.1 and Appendix C ("9,305", "5,479", "3,826",
     "13 times", "810 tracked library modules ... 808 passed ... Two unused
     legacy helpers ..."); Table 3 (Modules 795, Code lines 338,866, Check
     time 9,305 s); the last sentence of "Where the Workflow Failed" in
     Section 3.2 ("the two Lean modules of Table 1 that do not build").
   If there is no time to re-time: keep the numbers, and reword the
   footnote and those sentences to say that the two modules were removed
   after the measurement.
2. **The new text has not been checked by a second reader**: the Proof
   column and its legend, the sentence in step (6), and the appendix
   subsection. Points to check against the repository:
   * the codes per row (S for CNOT-dihedral rests on the header of
     `Examples/Groups/CNOT+Dihedral/Completeness.agda`, "the paper's
     Lemma 5.1");
   * the "Uses rows" column (4: 5; 5: 4; 11: 1; 12: 2; 13: 5; 14: 3;
     16: 1, 2, 6-9, 11, 12);
   * the commit-trailer counts (qudit 116 of 429; Toffoli-Hadamard 15 of
     28), from `git log` over the row's folders;
   * "about 3,400 lines ... in rows 3 and 9" (CCX+HH-TwoLevel's `Rel4`,
     `RelX4`, `Rel8`, `RelTau`, `QuadK2/Case*`; CNOT+Dihedral's
     `Linear/Local`, `Diagonal/LocalT`, `LocalX`: 3,383 lines).
   The page with Table 1 was not looked at after the column was added:
   check that no cell wraps badly.
3. **Page limit.** The main text is over 20 pages (Section 8 starts on
   page 21, the Data-Availability Statement is on page 22 in the test
   build). Deferred by the author; nothing was cut.
4. **Data-Availability Statement**: a draft with a `%% TODO (authors)`
   comment stands before the references; the authors write the final one.
   Proof scripts / supplement for submission: the authors'.
5. **Reference [9]** (`bian2027popl`) could not be found on the web; to be
   re-checked when the authors say it is out.
6. No cost or effort figures for the workflow (mock review A1): none
   exist; Section 3.2 gives commit counts and dates only.

## How to build

Build in a private copy, not in the working tree (other sessions edit it):
copy `pldi/` and `planqc/` side by side into a temporary folder (figures
are read from `../planqc/figures`) and run
`latexmk -pdf -interaction=nonstopmode -halt-on-error qcert.tex` in the
copy of `pldi/`. `pldi/qcert.pdf` is tracked: copy the built PDF back and
commit it with the source.

## Conventions

* Working copies are CRLF (`core.autocrlf=true`); run `unix2dos` on a file
  after writing it with a tool that writes LF.
* Fetch first, commit with explicit paths only, push to
  `origin ten-completeness`.
* The paper is double-blind: no title, tool name, author name or sentence
  of the draft in any web query.
