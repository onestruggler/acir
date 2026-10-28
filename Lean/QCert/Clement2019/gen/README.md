# Generators of the derivation modules

Python 3, no dependencies beyond the standard library.  The scripts use
`QCert/HadamardPi/gen/` (its search engine `deriv.py`, its lemma library
`lib.py` and exact arithmetic `q2.py`), which they import by path.  Run them
from this directory, one at a time:

```
python gen_conj.py     ../ConjLemmas.lean   # a few seconds
python gen_derivedc.py ../DerivedC.lean     # about three minutes ((21) is slow)
python gen_tables.py   ../Tables.lean       # about a minute
```

Every script checks each intermediate word of a chain numerically (exact
matrices over ℚ(√2), `q2.matrix`) before searching for the steps between
consecutive words, replays the steps it found (`deriv.check_steps`), and
writes the Lean steps; Lean checks them again by `decide +kernel`.  The
searches are deterministic, so the outputs are reproduced byte for byte.

| Script | Writes | Content |
|---|---|---|
| `clement.py` | — | Clément's relations (1)–(21) on `m` concrete indices as rewriting rules (`crules`; (20), (21) at every placement), the search engine over them (`CEngine`, a `deriv.Engine`), and a lemma library `CLib` whose lemmas are available at every injective placement (every increasing one with `inc=True`) and are emitted as `derC_map` instances.  A lemma is derived in `RelK false` ((1)–(19)) or `RelK true` (with (20), (21)) |
| `gen_conj.py` | `ConjLemmas.lean` | From (1)–(19): Lemma 3.5 ((22), following its printed proof), Lemma 1.7 (`X[1,0] ≈ X[0,1]`, `H[1,0] ≈ X[0,1] H[0,1] X[0,1]`) and the conjugation of every generator by `X[0,1]`, on at most four indices |
| `gen_derivedc.py` | `DerivedC.lean` | Figure 6's (d3) on four indices from (20) and (19), and (d4) on six from (21), along the chains described in the module's docstring |
| `gen_tables.py` | `Tables.lean` | For each of Clément's (1)–(19) and (22) and each arrangement of its indices, a Figure 6 derivation of its image under `tr`: a direct search, or for (19) a chain conjugating (f1) by the `X`'s of adjacent transpositions, letter by letter |
