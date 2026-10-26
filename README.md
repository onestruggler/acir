# qupit — Agda formalisation

Agda formalisation of group presentations, normal forms, and complete
relation sets for multi-qudit Clifford circuits.

## POPL artifact: source and linked HTML

The combined artifact (version `popl-revision2a`) is archived at
https://doi.org/10.5281/zenodo.23660617 as `acir-popl-revision2a.zip`.
Extract the entire archive. The repository root contains both the Agda
source files and the `html/` folder; no separate HTML download is needed.

To browse without installing Agda, open [`html/index.html`](html/index.html)
in a web browser, then follow the link to `MainTheorems`. Identifiers link
to their definitions. All required dependency pages and styling are included,
so the rendering works offline. Keep the complete `html/` folder together.
GitHub displays HTML source; download and extract the archive to browse it.

The rendering covers `MainTheorems.agda` and its transitive imports:
419 generated module pages, including 61 artifact modules and the required
Agda built-ins and standard-library modules. It does not cover every unused
module in the repository. See [`html/README.txt`](html/README.txt) for details.

The `popl-revision2a` archive contains the tracked files of commit
`df54a833f42d0ac7d5f2eebe05408c9109aa43c4`. It includes the changes that
made every module `--cubical-compatible` (commit `245f2315`, which also
rewrites the two proofs that used axiom K), and the HTML regenerated from
those sources on 2026-10-26. The archived snapshot retains references to
the preceding Zenodo version; the record above identifies this release.

To regenerate the rendering with Agda 2.8.0 and standard library 2.4, run
from the repository root:

```bash
agda --html --html-dir=html MainTheorems.agda
```

The software and accompanying software documentation use the MIT License;
see [`LICENSE.txt`](LICENSE.txt) for scope and exclusions. Dependency license
notices are retained in `html/AGDA-LICENSE.txt` and
`html/AGDA-STDLIB-LICENSE.txt`. Paper and other publication materials are
excluded from the MIT grant.

## Versions

| Component            | Version |
| -------------------- | ------- |
| Agda                 | 2.8     |
| Agda standard library| 2.4     |


The library configuration is in [`qupit.agda-lib`](qupit.agda-lib): it
includes the repository root (`.`) and depends on `standard-library`.

## Typechecking

Any of the following roots covers the whole live library:

```bash
agda Examples/Groups/Symmetric/Theorems.agda
agda Examples/Amalgamations/CliffordT1.agda
agda Examples/Amalgamations/QutritCliffordT1.agda
agda Examples/Amalgamations/U33Di.agda
```

`MainTheorems.agda` restates the headline theorems and typechecks
together with the roots above.
