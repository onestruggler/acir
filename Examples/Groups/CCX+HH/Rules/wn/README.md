# A derivation finder at any width

`finder.py` generalises the four-wire finder of `../w4/g4partial.py`
to N wires. The letters are the placed gates X, CX, CCX, SW and HH.
The relators are the natural rules at every adjacent placement, the
involutions, the commutations of disjoint adjacent letters, the
reversed CNOT as HH · CX · HH, and the other letters as swap conjugates
of adjacent ones, optionally with R4. Every relator is checked against
the exact matrices when the alphabet is built.

A target relator is traced by a partial proof-producing coset
enumeration over the affine group. The labels are kept canonical by
Gaussian elimination (`Alphabet.canon`), not by a table: AGL(5, 2) has
3.2·10⁸ elements. A norm step is an instance of affine completeness,
which holds at every width (`../../NaturalP/AffineComplete`). On four
wires it reproduces the four-wire finder (164 relators; the sign pair
commutes with CX1>0 in 5 s).

## The ctrl lemma's cores

NaturalP's ctrl lemma (`../../NaturalP/CtrlBounded`, `CtrlComm`,
`CtrlColour`) assumes completeness on at most eight wires. It applies it
only to fixed identities: each rule with its gates replaced by their
controlled gadgets (on one wire more than the rule: four wires for the
rules on three, five for those on four), the same under `ctrl₁`, and
the commutation cores. Deriving those identities directly would make
the lemma unconditional. That is the first step towards lowering
EveryWidth's base below twelve wires.

`ctrltest.py` tries the finder on the rules under ctrl, with the gadgets
as NaturalP writes them (`../ctrlcheck.py`). It derives only the two
smallest (X on a control, X through a swap). The rest fail fast, because
the gadgets are full of HH letters: the controlled CNOT is
HH · CCX · HH, so a controlled classical rule becomes a word of 50 to
240 letters, mostly HH. So the targets have to be restated before the
search:

- A classical gadget should be replaced by the classical word it equals
  (HH01 · CCX0;12 · HH01 by the letter CCX1;02, Fredkin by three
  Toffolis), each replacement a lemma on at most four wires. A
  controlled classical rule then becomes a classical identity on at most
  five wires, which is classical completeness there.
- Only the controlled-HH gadgets (CHHa, CHHb) are genuinely
  non-classical. Their identities are those of the HH rules under ctrl,
  six on four wires and one on five.

`ctrlclass.py` does that restatement for the classical rules. Two
changes to the finder make it work on four wires (`placed=True`): every
rule at every placement of its wires, and every two letters on
disjoint wires commuting. Each of those is a swap conjugate of an
adjacent instance in NaturalP. With them, all eight controlled rules on
three and four wires are derived, in 10–25 s each.

On five wires the schema is needed. The controlled Toffoli is
Barenco's T₁T₂T₁T₂, so a controlled rule with a Toffoli reduces, after
commutations, to (T₁T₂)⁴ = ε: the schema's first instance, which the
bounded rules do not derive (it lifts to −1 in the spin cover). With
it among the relators at every placement, ctrl(X0 CCX0 = CCX0 X0) is
derived (67 s). The other controlled Toffoli rules are not, at 30 000
cosets. They need five-wire commutations such as two Toffolis sharing
only a control, [CCX(1;0,2), CCX(4;2,3)] = 1. The finder does not
derive that at 60 000 cosets, though it derives two Toffolis with a
common target. That commutation is a genuinely five-wire fact: the
Toffoli-CNOT commutator would need a spare wire, and every wire is
used. So the cores on five wires and more need either classical
completeness there (a tower for A₃₂ would be many times the A₁₆ one) or
lemmas found by hand and fed to the finder, as `../w3/bootstrap.py`
did on three wires.
