# Compositional Verification of Qupit Clifford Circuit Equations

PLDI 2027 submission draft, revised after the mock review on
12 November 2026.

The paper explains the Agda formalization announced by the qupit
presentation, distinguishing it from the companion generic framework.
The central proof technique uses semantic head injectivity and
completeness one width below to certify the next coset table.

This revision also strengthens the formalization:

- Qupit-Clifford.Structural identifies the presented scalar extension
  with the independently defined structural Weyl group.
- Clifford+MinusOne.Qupit.Figure1.Structural carries the original
  sixteen-rule presentation to that structural group times the sign.
- Qupit-Clifford.Certificate certifies phase repair: a projectively
  valid replacement becomes an exact derivation with the computed
  scalar correction.
- Qupit-Clifford.CertificateExample checks a complete two-qutrit
  replacement: twelve gates become six, three CZ gates become one,
  and the certificate retains a computed nonzero scalar correction.
- Symplectic.Normalization.Computations evaluates nine closed
  normalizer equalities at primes 3, 5, and 7.

These results are indexed in MainTheorems.agda. The new literate
results section uses actual checked theorem aliases without postulates.
The complex-matrix interpretation and a full-circuit equivalence search
procedure remain outside the artifact.

## Manuscript layout

- Sections 1–2: contribution boundary, presentation contract, and a table
  identifying the semantic target at each layer.
- Section 3: qupit gates, circuit derivations, and semantic dependencies.
- Section 4: the coset normalizer, semantic well-definedness argument,
  uniqueness, and symplectic presentation.
- Section 5: Pauli composition, scalar extension, structural bridge,
  and the phase-repair certificate client.
- Section 6: proof-obligation comparison, validation, execution checks,
  development size, remaining limits, and AI Use.
- Sections 7–8: related work and conclusion.
- Data-Availability Statement and references.
- Appendices: permutation example; generic composition interface;
  detailed projective presentation variants and the rule figure;
  external matrix representation background; source inventory.

The paper uses acmart with
**acmsmall,screen,review,anonymous,nonacm**. The main text must fit within
**20 pages**, including AI Use. The Data-Availability Statement,
references, and appendices are excluded. See the
[PLDI 2027 call](https://pldi27.sigplan.org/track/pldi-2027-papers).
The revised PDF has 20 pages of main text and 29 pages overall.

## Sources and generated files

Edit main.tex, sections/*.tex, sections/*.lagda.tex, and refs.bib.
The six literate sections generate latex/vqupit/sections/*.tex;
do not edit those generated copies. The PDF and generated LaTeX are
tracked in this branch.

Most excerpts abbreviate module parameters and contain hidden
postulates. They are scope-checked for typesetting, not theorem
implementations. The exception is sections/results.lagda.tex, which
contains safe, fully typechecked aliases of the new results.
Check the library through MainTheorems.agda and the new excerpt
separately as below.

The script notes/stats.py counts retained .agda sources, including
blank lines and comments, excluding the external standard library
and literate sections. The revised snapshot has 247 files and 76,439
lines. Earlier notes/survey-*.md counts describe historical snapshots.

## Build and validate

Use WSL Agda 2.8.0 and standard library 2.4, registered in
~/.agda/libraries. Only standard-library is required.
From PowerShell at the repository root:

~~~powershell
wsl --exec agda +RTS -M5G -c -RTS MainTheorems.agda
wsl --exec agda +RTS -M5G -c -RTS vqupit/sections/results.lagda.tex
wsl --exec make -B -C vqupit agda
wsl --exec make -C vqupit
wsl --exec python3 vqupit/notes/stats.py
~~~

Run Agda sequentially. To reproduce the isolated fresh-project check:

~~~powershell
wsl --exec python3 vqupit/notes/check-artifact.py
~~~

The script copies project sources to a temporary Linux directory without
project interfaces and checks MainTheorems.agda with a 5 GiB compacting
heap. Installed standard-library interfaces are retained. If the heap
is exhausted, it checks the interrupted module separately and retries
the root, recording each attempt. It does not remove the checkout's
interfaces. Results and source fingerprint are written to
notes/validation/fresh-check.json; raw process logs are also written
there. The recorded run succeeded in one process: 442.867 seconds,
3,838,972 KiB peak RSS (3.66 GiB), on an i5-13400TEF under WSL2.
This is a build measurement, not a normalizer runtime benchmark.

After building, inspect main.log for errors, undefined citations and
references, and overfull boxes; render and visually inspect the PDF.
The nine execution checks are reflexivity proofs in the normalization
module, not uses of the corresponding circuit axioms.

## Remaining author work

The Data-Availability Statement records the intention to submit the
artifact for evaluation if accepted. PLDI also requests anonymized proof
scripts with the initial submission. Prepare and inspect that archive:
the checkout contains authors in the suppressed author block,
bibliography comments, and historical documentation. An anonymous PDF
does not anonymize its sources.

The introduction and related work acknowledge that version 2 of the
qupit preprint already announces scalar-sensitive verification and
refers to the companion formalization account. Review the contribution
boundary and publication status across both companion manuscripts;
include any manuscript described as supplementary material.

Review the new theorem statements, intended gate conventions, and
updated AI Use disclosure. The algebraic bridge is now checked; a
gate-preserving correspondence to the specified complex matrices is
still a substantive research task, as is a packaged full-circuit
equivalence procedure. The cited bibliography entries with missing metadata have been repaired;
notes/validation/bibliography-audit.json records the sources and corrections.

notes/submission-abstract.txt contains the copy-ready abstract.
Private submission administration and conflict notes are kept locally
and excluded from version control.

notes/freeze.py creates a hashed private snapshot beside the checkout;
its local notes/validation/freeze-manifest.json records the archive and
included file hashes. The snapshot contains author identities and is
not an anonymous proof supplement. Conference submission and reviewer
registration are separate from publishing this repository.
