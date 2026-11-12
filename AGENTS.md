# AGENTS.md

## Scope

This is `vqupit-pldi27`: the `vqupit/` paper, the Agda formalization it
describes, and their dependencies. Keep unrelated papers and developments
out of this branch. See `README.md` for the retained theorem chain.

`MainTheorems.agda` checks the qupit chain, the symmetric-group worked
example, the generic presentation constructions used in the paper, and
structural-rule independence. The retained library is its transitive
import closure together with that of `vqupit/sections/*.lagda.tex`.

## Validation

Use WSL Agda 2.8.0 and standard library 2.4. Register the standard library
in `~/.agda/libraries`. `qupit.agda-lib` depends only on `standard-library`;
EucDomain is not needed.

Always re-typecheck `MainTheorems.agda` after editing library files:

```powershell
wsl --exec agda MainTheorems.agda
```

Invoke WSL directly from PowerShell, since Git Bash can mangle paths.
For memory-intensive checks, use `+RTS -M5G -c -RTS`; if a fresh root
check exhausts memory, check the module it stopped on separately and
rerun the root. Do not run Agda processes that write the same interfaces
at the same time.

After editing a literate paper section, regenerate it and build the PDF:

```sh
make -B -C vqupit agda
make -C vqupit
```

The paper snippets use `--only-scope-checking` and hidden postulates for
abbreviated statements. They are not substitutes for checking the actual
proofs, which must remain safe and hole-free.

## Conventions

- Follow `style-guide.md`: 72-character banner headers, the library line
  `-- Presentations of groups`, `--safe`, and explicit imports.
- `_===_` is the raw axiom relation; `_≈_` is its monoid congruence.
- `[_]ʷ` injects a generator; `(f ʷ)` extends a word-valued map to words;
  `(h ᵗ)` extends a coset action to words.
- `nfp` and `nfp'` name normal-form witnesses. Open or project them through
  `Normalization.NormalForm.Setoid`, since the propositional variants
  are aliases.
- Keep full theorem signatures in `MainTheorems.agda` and put proofs in
  their home modules.
- Avoid `with`-abstracting large terms at symbolic p in the scalar
  development; destructure them in helper functions to avoid normalizing
  the entire goal.
