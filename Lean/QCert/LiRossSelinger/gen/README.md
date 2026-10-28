# Generators for the derivation tables of Lemma A.20

Python 3 with `numpy` (only `plan323.py` uses it).  Run every script from
this folder; set `PYTHONHASHSEED=0` (the searches do not depend on it, but it
costs nothing).  The searches write JSON here; the emitters read the JSON and
write the Lean modules in the parent folder.  Regenerating reproduces the
committed modules byte for byte.

## Searches (write JSON)

| script | writes | what | time |
|---|---|---|---|
| `boot.py` | `boot.json` | chains on `0..3` for (8a)–(8d), (9a)–(9g) and `K (−1)_a K ≈ X_bc (−1)_a K (−1)_a`, each with the earlier ones as macros (BFS through waypoints) | seconds |
| `plan1223.py` | `d1223.json` | (6a) and Proposition A.16 as `W⁻¹ C W ≈ C` on `0..7` | seconds |
| `plan325.py` | `d325.json` | Subcase 3.2.5: `K ≈ V K S` (8 sign patterns), `K S' K ≈ V K S` (64) on `0..3` | about a minute |
| `plan323.py` | `d323.json` | Subcase 3.2.3: the 96 relations on `0..3, c, d` (`c, d = 4, 5`) | several minutes |

## Emitters (write Lean)

| script | reads | writes |
|---|---|---|
| `mkderive.py` | `boot.json` | `../Derive.lean` from the marker `Derived relations (generated)` on (the macros are flattened to Table 1 steps) |
| `mk1223.py` | `d1223.json` | `../Rel1223.lean` |
| `mk325.py` | `d325.json` | `../Rel325.lean` |
| `mk323.py` | `d323.json` | `../Rel323.lean` |
| `mkmeet.py` | `meet_head.lean`, `meet_tail.lean` | `../CaseKMeet.lean` (the `par_ij` and `two_ij` cases between head and tail) |
| `mkx8.py` | — | `../CaseX8.lean`, the region `eight_lev_e`, `eight_lev_h` only |

```
python3 boot.py && python3 plan1223.py && python3 plan325.py && python3 plan323.py
python3 mkderive.py && python3 mk1223.py && python3 mk325.py && python3 mk323.py
python3 mkmeet.py && python3 mkx8.py
```

## Library

* `rules.py`: the families of Table 1 with the index conventions of
  `Checker.sides`; `macros.py`: the derived relations; `sides2.py`: sides of
  any step (`rev_` for a relation read backwards), `apply_all`, commuting
  disjoint blocks.
* `bfs.py`, `chain.py`: bidirectional BFS for a derivation, through
  waypoints.
* `sp.py`, `sptools.py`: signed permutations; derivations between words of
  `(−1)` and `X` letters by normalising one letter at a time (a small BFS
  per letter, memoised).
* `passtools.py`: `refactor`, rewriting `σ K_S τ` into `σ' K_S' τ'` for
  semantically equal words, by passing the generators of `σ'⁻¹ σ` through
  `K` one at a time (relations (4a), (4c), (8a)–(8d), (9a)–(9f), (2c),
  (2e) and the renamings (3d)–(3g)), found by a BFS in the group.
* `flatten.py`: expands macro steps into Table 1 steps; `leanfmt.py`: Lean
  syntax for words and steps; `alg.py`: an exact model of Algorithm 1.

## Numerical checks (not needed to regenerate)

`t1223.py` (both diagrams of Subcase 1.2.2.3 with `u_e` odd, levels of every
state), `t32.py` (Case 3.2: which subcases occur below the level, the shape
`V K W`), `t323.py` (sign patterns of Subcase 3.2.3), `ta16.py` (relation
(6a), Proposition A.16 and the lines of its printed proof).
