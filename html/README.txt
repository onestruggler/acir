# Linked Agda HTML for the POPL artifact

Extract the entire acir-popl-revision2.zip archive, then open html/index.html
inside the acir-popl-revision2 directory in a web browser. Start with
MainTheorems.html. Click highlighted identifiers to jump to their definitions.
Keep all files together: links and styling use relative paths. No Agda
installation, internet access, or local web server is needed to browse.

This package renders MainTheorems.agda and all modules imported transitively
by that entry point, including Agda built-ins and standard-library dependencies.
It is not a rendering of unrelated files or every unused module in the repository.

Source: the Agda files of the popl-revision1 release, commit
5e28af3f344c11b27096c012c2f7b7be4cc51bf5, as changed by commit 245f2315,
which adds --cubical-compatible to every module and rewrites the two proofs
that used axiom K. The Agda sources and this html/ folder are included
together in the same repository. The top-level README.md gives the source
typechecking instructions.

Generated and typechecked on 2026-10-26 using Agda 2.8.0 and standard library 2.4
on Linux under WSL. From the repository's top-level directory, run:

    agda --html --html-dir=html MainTheorems.agda

The command completed successfully, with a pre-existing UselessPrivate warning
in Presentation/Construct/Properties/Extension.agda. The landing page,
README, and license notices were added after generation, and the link-check
report was recomputed for this rendering (419 module pages, 61 of them
artifact modules, no broken links).

Archive version: popl-revision2 (this rendering postdates the archived one)
Zenodo DOI: https://doi.org/10.5281/zenodo.23636192

License: see PROJECT-LICENSE.txt for the artifact's software/documentation,
AGDA-STDLIB-LICENSE.txt for standard-library pages, and AGDA-LICENSE.txt for
Agda built-ins and the generated stylesheet. Existing notices in the rendered
sources remain applicable.
