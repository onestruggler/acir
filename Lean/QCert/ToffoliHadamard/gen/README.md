# Generators of the ToffoliHadamard derivation tables

Four modules of the folder above are generated; everything else is written
by hand.

| Module | Script | Inputs |
|---|---|---|
| `Micro.lean` | `emit_micro.py` | `data/micro.json`; `../Syntax.lean` (Figures 4, 7, `(r_K)`) |
| `MacroTable.lean` | `emit_macro.py` | none (the rewriting system of `S₈` and the 630 transport certificates are computed by `transport.py`, `kb.py`, `macro.py`) |
| `Families.lean` | `emit_fam.py` | none |
| `RoundTable.lean` | `emit_round.py` | `data/routes.json`, `data/rt_lrs.json` |

`Gens.lean`'s list `allAG` is the 106 generators in the order of
`transport.gens8()`.

## Regenerating

From this folder, in Linux (here WSL; Python 3 with no extra packages, and
`gcc`):

```
./run_all.sh emit     # the four modules from the recorded data/ (seconds)
./run_all.sh          # every search again, then data/, then the modules
```

Both reproduce the committed modules byte for byte.  The emitters also run
on Windows Python (`python emit_micro.py`, …); an optional argument is the
output path.

## The searches (`./run_all.sh`, about 20 minutes)

`bfs.c` is a bidirectional breadth-first search over words of involutions
whose rules are the rotations of relators (a relator `u v` gives
`u → rev v`).  It is compiled twice, with 5-bit letters (`bfs`, the 25
letters of `Σ₁`, words of at most 25 letters) and 7-bit letters (`bfs7`,
the 106 generators of `𝒢₈`, at most 18):

```
gcc -O2 -o bfs bfs.c
gcc -O2 -DBITS=7 -o bfs7 bfs.c
```

It reads the alphabet size, the longest rule left side and the relators,
then queries `mode maxlen limit maxgrow  na a…  nb b…` on standard input,
and prints the steps found (`cbfs.py`, `lrsc.py` drive it; on Windows
through `wsl --exec`).  Its choices are deterministic: the frontier is
expanded in order, and at each position the rules are tried by length of
left side and then from the most recently added (`bfs`), or, with
`bfs --first`, by first letter in the order they were added — the order
the saturation step (3) was run in, which `sat2.py` asks for.

The steps write their results to `work/` (not committed), each from the
previous ones:

1. `s01_involutions.py`: every letter of `Σ₁` is an involution (plain
   steps over `R₁`, `search.py`).
2. `s02_enum.py`, `s03_relators.py`: all relators of length at most 6
   between words of `Σ₁` (by their matrices, `fastmat.py`).
3. `sat2.py 10 200000 8 4,5,6`: derive as many of them as the search
   finds, round after round, each added to the rules once derived.
4. `s05_coxeter.py 6 3000000 2`: the Coxeter relations of the words
   `xAdj i`; `s06_x34.py 1500000 10`: those of `X_[3,4]` through
   `xAdj 3 = P X_[3,5] P⁻¹` (the pieces); `s07_store.py` collects all
   derivations; `s08_assemble.py` assembles the remaining Coxeter
   relations from the pieces.
5. `s09_mfacts.py`, `s10_routes.py`: the facts and routes of the round
   trip.
6. `s11_lrs.py`: derivations in Li–Ross–Selinger's Table 1 for
   `Z₀ Z₁ Z₂ CZ₀₁ CZ₀₂ CZ₁₂ K₀₁ K₁₂` (`lrs.py`, `lrs3.py`, `lrsc.py`).
7. `s12_export.py`: writes `data/micro.json` (the 450 relators `Micro.lean`
   uses, with their derivations, and the involutions), `data/routes.json`,
   `data/rt_lrs.json`.

`famcheck.py` checks in Python that the bubble-sort and palindromic paths
are valid for every instance of Table 1 (the Lean check is
`Families.lean`); `model.py` and `rels.py` are the matrices and relations
of the paper; `tc.py` is a coset enumeration used while choosing the
search strategy.
