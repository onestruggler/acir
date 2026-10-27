# Derivation search

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
