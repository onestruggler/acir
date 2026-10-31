# Three-qubit Clifford+CS certificate construction

These scripts use the Lean presentation and exact gate matrices. They do
not read any Agda development. Matrix calculations propose statements;
all completed statements are justified by Lean derivations from Figure 2
and the already proved two-qubit presentation.

Run from this directory with Python 3:

```
python3 three_words.py
python3 emit_atom.py 5
python3 emit_atom.py 12 extra
python3 emit_atom.py 12 negative
python3 local_block.py
python3 emit_local_block.py
python3 emit_phase_conjugation.py 0
python3 emit_phase_white.py 0
python3 emit_phase_point.py 3
python3 emit_phase_opposite.py 0
python3 emit_factor.py
python3 emit_rotation.py
python3 emit_recovery.py 0
python3 permutation_certificate.py
python3 emit_permutation_routes.py
python3 emit_permutation_frames.py
python3 emit_permutation_block_frames.py
```

The `data/` JSON files retain only the proof DAGs used by the completed
four-letter certificates. Regeneration does not require re-running a
completion search. `three_words.py` constructs and exactly checks the
Gray-path transpositions, the one-point sign, and the residual Hadamard
atom. `local_block.py` replays a small completion problem on the residual
Clifford group; its six group identities and the transposition definition
are proved in `Three/LocalKZ.lean`.

`coset_checks.py` enumerates and numerically checks all 98 finite macro
obligations. Those numerical checks are diagnostics, not completeness
proofs. `pair_normalize.py`, `search_atom.py`, and `search_white.py` are
search tools; unfinished searches do not contribute a Lean theorem.

The certificate replay uses `decide +kernel`, never `native_decide`.

The four `emit_phase_*` scripts retain their proof DAGs in `data/` and
regenerate their Lean certificates without running a search. They prove
the pair phase's action on a controlled exchange, commutation on a
complementary control, the pair phase's action on the residual atom, and
commutation of the atoms on opposite controls. Their consumers are
`Three/PhaseDressed`, `Three/PhaseStabilizers`, `Three/PhasePoint` and the
optional opposite-control lemma. The `search_phase_*` scripts are exploratory
completion searches; only the emitted, kernel-checked derivations enter
the proof.

`emit_recovery.py` replays the retained `AtomRecovery-seed0.json` proof DAG
for removal of one control from the residual Hadamard. The other control
is removed by the proved two-qubit presentation. `search_recovery.py`
records how the first certificate was found; regeneration uses the JSON
directly and does not require its temporary search caches.

The permutation exporters translate the existing independent Lean
permutation certificates and normalize Coxeter words with explicit
rewriting proofs. They supply all token relations, the permutation
identities for generator recovery, and the frames for the final Hadamard
equations. `Three/Certificate.lean` checks the complete 98-case table;
`Three/GeneratorRecovery.lean` checks recovery of all nine generators.
