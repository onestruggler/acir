# Generators for CCX+HH-3qubit-opus

Python 3 (no dependencies) and a C++17 compiler. Run from this directory.

| Script | Writes |
|---|---|
| `search_all.py` | `derivations.json`: the level-0 lemmas derived from Figure 4, found by search (cached lemmas are replayed in their recorded order, not searched again) |
| `mk_all.py` | `../Toffoli/Base.agda`, `../Toffoli/Lemmas.agda`, `../Toffoli/Coxeter.agda` |
| `mk_derived.py` | `../Derived.agda` |
| `mk_push.py` | `../Push.agda`, `../PushMatrices.agda` |
| `mk_indep.py` | `../Independence.agda` |
| `gen_circuits.py` | `../Circuits/Syntactics.agda`, `../Circuits/Iso1.agda`, `../Circuits/Iso2.agda`, from `../Syntactics.agda` |
| `errata.py` | nothing: it checks every claim of `../ERRATA.md` on the matrices |

```sh
g++ -O2 -std=c++17 -o fbfs fbfs.cpp
python3 search_all.py
python3 mk_all.py && python3 mk_derived.py && python3 mk_push.py && python3 mk_indep.py
python3 gen_circuits.py
```

With `derivations.json` as committed, the four `mk_*` scripts reproduce the
Agda modules byte for byte.

## The search

`model.py` is the numerical model (exact 8 × 8 matrices over the rationals,
basis state `4 x₀ + 2 x₁ + x₂`, words in operator order), and `rels.py` the
relations of `Syntactics.agda`; every target is checked against the model
before it is searched for.

The bootstrap lemmas (every gate an involution) use the axioms as written.
After that a lemma `l = r` is also used through every rotation and split of
its relator `l r⁻¹` (`closure.py`), which is what the engine's `rot⁼`
replays. `search.py` is a bidirectional breadth-first search in Python and
`fbfs.cpp` the same search in C++ over words packed into 128 bits (at most 25
letters), about a hundred times faster; `rounds.py` tries a pool of targets
in rounds of growing budget, so that easy lemmas are available to the hard
ones.

`targets.py` lists the targets: the conjugation tables of the swaps and the X
gates, the short forms `U d` of Figure 7's circuits `T d` (`perms.py` finds
shortest words over the permutation gates; `T 3`, eleven gates, goes through
five nested conjugations), the Coxeter relations for the `U d` (braids through
a shortest word for `X_[i,i+2]` as a midpoint), and the identities that lead
from the `T d` to every gate. `mk_all.py` turns the Coxeter relations for the
`U d` into those for the `T d` by substitution.

`hconj.py` finds short words for the conjugates `H₂ g H₂` of the gates, which
`mk_push.py` uses for Lemma 6.1.
