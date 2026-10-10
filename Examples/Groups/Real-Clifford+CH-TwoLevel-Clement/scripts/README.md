# Generators for Real-Clifford+CH-TwoLevel-Clement

Six modules of this development are generated. These scripts regenerate them
byte for byte. They need Python 3 and nothing else.

```bash
cd diagrams && python gen.py    # Diagram20.agda, Diagram30.agda
cd trees    && python gen.py    # NFs.agda, TreeNF341.agda, TreeNF38.agda, TreeTop.agda
```

Each `gen.py` writes into the development's folder (two levels up), or into the
directory given as its argument.
Both pass their output through `tidy.py`, which drops the imported names and
the one-line helpers that a module does not use.

## `diagrams/`: Clément's diagrams (20) and (30)

`gen.py` derives each diagram, read as a relator `Route = H[0,1]`, from
Clément's relation (20) or (21) on the first four or six indices. The
derivations are explicit chains (`manual.Chain`), each step checked as it is
built: `perm` moves to a word equal up to commuting letters (`deriv`), and
`rw` rewrites by a named equation (the hypothesis, or a local relation). The
checked chains are emitted as `derive` proofs for
`Real-Clifford+CH-TwoLevel.Engine` (`emit.py`).

- `routes.py`: the two cores, as operator-order letter lists.
- `words.py`: Clément's (20) and (21) as letter lists.
- `deriv.py`, `manual.py`: the step checker and the chain builder.
- `emit.py`: the Agda text.

## `trees/`: the decision trees

`trees.py` builds the trees that `Tree.agda` checks and `Sound.agda` interprets.
`core.py` mirrors `Forms.agda` and `Check.agda` exactly: linear forms over
ℤ[√2] (numbers are pairs (a, b) = a + b√2), halving, parities, classes, and the
route check. When a parity or class the check needs is not determined, it
raises `Dep`, and the search splits on it.

- Normal forms (`NF38`, `NF341`). These are Clément's (38) for Subcase 3.4.2,
  and the form of Subcase 3.4.1. Each has a subtree of decorated diagrams. In
  (38), Subcase 3.4.2.3 adds rows of depths 2, 2 and 3 (`stage3`), and then
  conjugates by H on a row of depth 2 and the row of depth 3 (`stage4`).
- The top tree (`top`). It starts from the root forms of a hard state's window
  (c, d, e, f). It decides the classes at H_ce H_df s, adds the two extra rows
  of depth 1 (`extend`), and reaches a normal form by a swap of the pair, signs
  (`conj` Z) and a change of variables (`reparam_solve`).
- `emit.py`, `gen.py`: the Agda terms, and the modules with their `refl`
  checks.

Splits are chosen greedily among the dependencies that failing candidates
raise. A different choice gives different but equally valid trees, so the
output is deterministic only because the search is.
