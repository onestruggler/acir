# Derivation search

## CNOT-dihedral (Appendix H)

`search.py` searches for derivations in a PROP presentation on the
framework's circuits: words of generators `(gate, wire)` in operator order,
moves the rewrites by the instances of the axioms, of the laws of the
symmetry, of the structural scalar rule and of lemmas already found, at
every placement, and the exchange of adjacent generators on disjoint wires;
a breadth-first search from both ends.

`cnot.py` is CNOTdihe₂ (Figure 7) and the relations of Amy, Chen and Ross;
`run_all.py` finds the derivations (`cnot_derivs.json`) and `gen_cnot.py`
writes `../CNOTDihedral/Derivations.lean`, whose steps `derive` replays.

    python run_all.py && python gen_cnot.py

## The appendices, line by line (Cliff₂, RCliff₂)

* `figparse.py` reads a figure of the paper (a TikZ picture compiled to
  PDF) into gates: boxes with their labels, control dots and targets on a
  vertical line, crossings of wires, scalars.  `figs.py` caches the figures
  (`figures.json`) and the derivations of the appendices as chains of
  figures with the labels cited between them (`derivations.json`); the
  paper's source is only needed to refill them (`BLAKE_SRC`).
* `cliff2.py`, `rcliff2.py`: the rule sets of Figures 2 and 3, the figures
  as words (the shortcuts of Figure 9 expanded), exact matrices to check
  every line, and the intermediate lines added where the search needs them
  (`EXTRA`).
* `tsearch.py`, `tsearch2.py`: words modulo commuting gates on disjoint
  wires (canonical forms, occurrences of a side up to commutation), scalars
  collected in front, cancellation of `x^k = ε` (`H²`, `S⁴`, `CX²`, `σσ`,
  scalars), registered commutations (Cliff₂'s (C)), relator-style partial
  rewriting; every move is turned into the `rw`/`swap` steps of `derive`.
* `variants.py`: derived forms of an equation with mechanical derivations:
  both sides inverted, upside down (conjugated by the swap), the three
  wires reversed.
* `driver.py`: a derivation through given lines; each step tries the rules
  cited for it, their derived forms, the neighbouring steps' rules, partial
  rewriting, and steps drawn upside down.
* `run_cliffd.py`, `run_rcliff.py` find the derivations (`*_cache.txt`);
  `gen_cliff.py`, `gen_rcliff.py` (with `gen_frag.py`, `leangen.py`) write
  `../Clifford/Derivations.lean`, `../RealClifford/Derivations.lean`.

      python run_cliffd.py && python gen_cliff.py ../Clifford/Derivations.lean
      python run_rcliff.py && python gen_rcliff.py ../RealClifford/Derivations.lean

  With the caches present this reproduces the files byte for byte; with a
  cache removed the search runs again (minutes).
