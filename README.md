# qupit — Agda formalisation

Agda formalisation of group presentations, normal forms, and complete
relation sets for multi-qudit Clifford circuits.

## POPL artifact: source and linked HTML

The combined artifact (version `popl-revision2`) is archived at
https://doi.org/10.5281/zenodo.23636192 as `acir-popl-revision2.zip`.
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

The archived `popl-revision2` sources are those of the `popl-revision1`
release (commit `5e28af3f344c11b27096c012c2f7b7be4cc51bf5`). The repository
has since made every module `--cubical-compatible` (commit `245f2315`, which
also rewrites the two proofs that used axiom K), and the rendering here was
regenerated from those sources on 2026-10-26.

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
