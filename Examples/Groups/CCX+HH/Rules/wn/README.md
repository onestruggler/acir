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
