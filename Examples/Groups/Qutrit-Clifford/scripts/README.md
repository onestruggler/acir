# Generators for Examples/Groups/Qutrit-Clifford

Python 3 (no packages) and Perl; run from this directory.  Words are
lists of gates, and every script that writes Agda checks its data
against an exact model first: `qt.py` computes qutrit Clifford circuits
over F₇ (ω = 2, 1/(ω² − ω) = 4, −ω = 5), which is faithful for these
finite groups.

| Module | Generator |
| --- | --- |
| `Axioms.agda` | `python3 gen_axioms.py` (reads `Syntactics.agda`) |
| `NormalForm.agda` (box section) | `python3 gen_nf.py`; `check_nf.py` checks it against `boxes.py` |
| `Tables.agda` | `python3 emit_tables.py ../Tables.agda` (the 380 box relations of `boxrel.py`, typed by `tables.py`) |
| `Z3.agda` | `perl gen_z3.pl > ../Z3.agda` |
| `Pauli.agda` | `perl gen_pauli.pl > ../Pauli.agda` |
| `Uniqueness.agda` | `python3 gen_uniq.py` (box actions from `pauli_act.py`) |
| `Box1.agda` | `python3 kb_one.py` (Knuth–Bendix on C1–C5) |
| `Box2.agda`, `Box2/Part*.agda` | `python3 br2gen.py emit 2000` (Felsch enumeration, `felsch.py` on `relcos2.py`, `relcos.py`, `kb.py`, `coset2.py`; relations from `br2rels.py`; Agda from `emit2.py`) |
| `Box3.agda`, `Box3/Part*.agda`, `Box3/Steps*.agda` | `python3 br3gen.py && python3 emit3.py 10` (each relation a loop in the graph of hyperbolic planes of F₃⁶, `geo.py`, filled by translates of the loops of C15–C18, `fill.py`; the derivations pass through `br3.pkl` in the working directory, and each distinct two-wire step is a lemma of `Box3/Steps*`, decided once) |

`rules.py` checks the 18 rules and `boxes.py` the boxes' Figure 8
actions in the model.  The paper's Figure 25 (third row) is misprinted —
`boxrel.py` uses the corrected relation.
