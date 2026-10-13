# The two-wire derivations

`run.sh` regenerates `Lemmas/TwoWire.agda`, `Lemmas/TwoWireMacro.agda`
and `TwoQubit/Decoding.agda`: Lemmas 7.4 and 7.5 of the two-qubit
back-and-forth argument (`TwoQubit`), i.e. the decoding of the two-level
generators on four indices inverts the encoding of the gates and sends
each of the 118 instances of Bian and Selinger's relations to an
equation derivable from the rules of `Syntactics` on two wires.

    bash run.sh [WORKDIR]

needs `g++` and `python3` with `numpy`, and takes about five minutes.

## Files

- `kbc.cpp` — Knuth–Bendix completion of a monoid presentation that
  records, for every rule, a derivation from the rules before it, and
  dumps the derivations of its targets and of every rule they use.
- `model.py` — the alphabets, their matrices, the decoding (`D`, letter
  for letter `TwoQubit.d`), the 118 decoded instances, and what each
  stage proves; `python3 model.py` checks every equation numerically.
- `emit.py` — turns kbc's output into definitions for `Engine`.
- `generate.py` — kbc's inputs, and the three Agda modules (with the
  headers `*.head`).

## The pipeline

The decoded relations are long words on the gates (up to 232 letters,
`order-K` on the indices 0, 3), but short over the circuits they are
written with — X, X↑, CX₀₁, CX₁₀, CK₀₁, CK₁₀, CS, S, K and the scalar —
at most 40.  So they are derived over those as letters (**tier 2**, in
`TwoWireMacro`), from some eighty equations between them, each of which
is proved on the gates (in `TwoWire`).  That takes three stages, because
a completion of the rules on two wires does not by itself reach the
Clifford equations about the swap (that CX₀₁ CX₁₀ CX₀₁ = CX₁₀ CX₀₁ CX₁₀,
how it conjugates the Paulis, …):

- **stage 0**: Selinger's presentation of the two-qubit Clifford group,
  C1–C11 read with H = ω K and CZ = CS² — C8–C11 are the only ones that
  take work, and C10 is C11 with the wires exchanged;
- **tier C**: from those, the Clifford equations, by a completion over
  the Clifford gates with CZ as one letter: the group is finite, and the
  completion decides them in seconds.  Its derivations are printed on
  the gates, CZ written CS CS;
- **stage 1**: the equations involving CS and the controlled K gates,
  from the rules and the Clifford equations;
- **tier 2a**: five of the macro equations are consequences of the
  others over the macro letters (swap conjugations), and are derived
  there.

The completions run on the letters with wire 1's scalar read as the
scalar; the three rules that differ are restated in `TwoWire`'s header
with `ω↑=ω`.  This makes the rules symmetric under exchanging the wires,
and a completion is not (its order is not): an equation one run misses
is often the mirror image of one another run finds, and is replayed
mirrored (stages 0 and 1 run both ways; mirrored rules are named `m…`).

The queue matters.  Processing the oldest rule first, a completion with
eighty axioms buries a three-step consequence under a hundred thousand
rules; processing the shortest first finds it at once.  Every stage but
tier 2 runs shortest first.  A smaller `maxlen` also gives smaller
proofs (tier C uses 232 rules at 16, 2091 at 24).

## The Agda format

A derivation is checked by running it (`Engine.derive l r steps refl`),
so what is elaborated is the list of steps.  Positioned rewrites whose
types spell the intermediate lists (`take k w ++ r ++ drop … w`, which
mentions the previous list twice) double the elaborated term at every
step: the same derivations took 96 s and a 3.9 GB residency that way,
10 s and 0.4 GB as `derive`.
