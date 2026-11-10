# The alternating group on sixteen points as reversible circuits

The circuits on four wires over NOT (`X`), CNOT (`CX`), Toffoli (`CCX`) and
the swap of two adjacent wires (`Ex`) carry out exactly the even permutations
of the sixteen states of the wires. This folder proves that seven rules
between such circuits present Alt(16):

    r1 : X • X                       = ε
    r2 : CX • X↑ • CX • X↑           = X
    r3 : CX • CX↓ • CX               = Ex
    r4 : CCX • X↑↑ • CCX • X↑↑       = CX
    r5 : Ex↑ • CCX • Ex↑             = CCX
    r6 : CX↓ • CCX • CX↓             = CCX↓ • CCX • CCX↓
    r7 : CCX↑ • CX • CCX↑            = CCX₃₂₀ • CX

together with the laws of the swap of `Circuit/Prop.agda` (the swap is an
involution and natural in every gate) and the structural rules of
`Circuit/Base.agda`. They are the rules of `XCXCCX-4bit/Syntactics.agda`
(Figure 1 of *Block Normal Forms and Certified Equations for Four-Bit
Reversible Circuits*), restated word for word over this folder's gates
(`Theory.agda`); nothing else of that development is used.

The presentation is obtained from Lafont's presentation of Alt(16) by cycles
of three consecutive points (`Examples/Groups/Alternating`, his Theorem 4) in
two Reidemeister–Schreier steps, each laid out as
`ProjectiveClifford/Qupit/Paper-V0/Iso.agda`: translations of the generators
in both directions, and the two relation sets shown equivalent along them.
`MainTheorem.agda` is the entry point:

- `presentationᴿ : (4 RRel,_===_) IsPresentationOf Alt-group 16`, a circuit
  read as the even permutation `⟦ w ⟧ᴬ` of the positions of the states;
- `soundᴿ`, `completeᴿ`: two circuits are equal by the rules exactly when
  they are the same function on the states;
- `normal-formᴿ`, `nf-congᴿ`, `canon-g`, `nf-canon`, `canon-unique`,
  `canon-onto`: every circuit is equal by the rules to a unique canonical
  circuit, the translation of Lafont's canonical form letter for letter;
- the first step, `circuits≅cycles` with `f-well-defined`, `g-well-defined`,
  `f-left-inv-gen`, `g-left-inv-gen`, and its `presentation` of Alt(16) by
  the translated relation;
- the second step, `relations⇒rules`, `rules⇒relations`, `rules≅relations`
  (the identity is an isomorphism of the two word groups) and `rules≅cycles`
  (the first step holds for the rules, with the same translations);
- `presentation₁`, `presentation₂`, `presentation₃`, `complete₁`, …: on one,
  two and three wires the rules present S₂, S₄ and S₈.

Nothing is postulated, and every module is `--cubical-compatible --safe`.

## Conventions

Wire 0 is the bottom wire. `CX` has its control on wire 1 and its target on
wire 0, `CCX` its controls on wires 1 and 2 and its target on wire 0, and
`Ex` swaps the wires 0 and 1; `w ↑` is w one wire up. `CX↓ = Ex • CX • Ex`
and `CCX↓ = Ex • CCX • Ex` have control and target exchanged, and `CCX₃₂₀ =
Ex • CCX↑ • Ex` has its controls on the wires 2 3 and its target on wire 0.
Words are in diagram order: `w • v` is w followed by v, on both sides
(Lafont's words too).

A state is a vector of four bits, the bit of wire 0 first. The sixteen
states are numbered along the reflected Gray code, wire 0 changing most
often: position i is the state i xor (i >> 1), bit k of it on wire k
(`Numbering.enc`, `dec`). Written with wire 3 first:

     0 0000    4 0110     8 1100    12 1010
     1 0001    5 0111     9 1101    13 1011
     2 0011    6 0101    10 1111    14 1001
     3 0010    7 0100    11 1110    15 1000

Lafont's cycle ωᵢ sends position i to i + 1, i + 1 to i + 2 and i + 2 to i.
Two consecutive states differ on one wire, so the states i, i + 1, i + 2
are three corners of a face of the 4-cube with the other two wires fixed,
and their cycle is a doubly controlled cycle of three states of two wires:
the commutator of two Toffoli gates. `K = (Ex₀ • Ex₂ • CCX) ^ 4` is the
cycle of the positions 9, 10, 11, and `Ω i`, the circuit of ωᵢ, is K carried
to the right face by swaps and to the right corner by NOT gates
(`Syntactics`; 12 to 24 gates).

## The first step: Lafont's words and circuits

**The generators, in both directions** (`Translation`). `g` reads a cycle as
a circuit, `g ωᵢ = Ω i`. `f` reads a gate as a word in the cycles, the
permutation of the positions that the gate carries out: the six gates on
their own wires have words of 8 (`X`), 4 (`CX`), 6 (`CCX`), 8, 12 and 24
letters (the swaps of the wires 0 1, 1 2 and 2 3), and a gate on other wires
goes to the word of that gate between the words of the swaps that carry it
there.

**The two relation sets.** Lafont's (`Alternating/Syntactics`, at width 16)
are ω ω ω = ε, ω ω↑ ω = ω↑ ω↑ and ω ω↑↑ ω = ω↑↑ ω ω↑ at every position, and
the commutation of two cycles three or more points apart. The translated
relation on the circuits (`Syntactics`, on four wires) has

- those relations read between the circuits Ω i: `order i` (i ≤ 13), `near
  i` (i ≤ 12), `far i` (i ≤ 11) and `apart i j` (i + 3 ≤ j ≤ 13), that is
  14 + 13 + 12 + 66 = 105 instances;
- six gate rules `gate-X`, …, `gate-Ex₂`, each saying which word in the Ω i
  a gate on its own wires is;
- the laws of the swap and the structural rules.

**They are equivalent along the translations** (`Iso.Theorem`):
`f-well-defined`, `g-well-defined`, `f-left-inv-gen`, `g-left-inv-gen`. The
half towards the circuits is syntactic (`Lemmas`): an instance of Lafont's
relation read through g is one rule, and a gate is the circuit of its word by
its gate rule or, further up, by the naturality of the swap. The half towards
Lafont's words is semantic: a word in the cycles permutes the positions as
its circuit maps the states (`Bridge.f-sem`, `g-sem`), the rules are sound
for functions on states, and two words in the cycles with the same
permutation are equal by Lafont's completeness. `Presentation.Morphism`'s
`StarGroupIsomorphism` makes `f ʷ` a group isomorphism
(`Theorem-Circuits-iso-Cycles`), and `Presentation` composes it with Lafont's
theorem.

**The normal form** (`NormalForm`). Lafont's canonical form of an even
permutation is a product of stairs, runs of cycles ω₀ ω₁ … that bring a point
to position 0. Read through g, a stairs is `Ω d • Ω (1 + d) • …` (`stairs`),
a canonical circuit is the product of its stairs (`canon`, `canon-g`), and
the normal form of a circuit is Lafont's normal form of its word. Lafont's
`nf` works by rewriting, and on the word of a circuit it passes through
millions of letters, so it should not be run; to compute a normal form, read
it off the permutation (`nf-sem`).

## The second step: the translated relation and the rules

The two relation sets are over the same gates and the translations are the
identity, so the step is that each set's rules are consequences of the
other's.

**From the rules to the translated relation** (`Theory.t⇒s`) needs no
derivation: the rules hold for functions on states (`T-sound`), for which
the translated relation is complete.

**From the translated relation to the rules** (`Equivalence.s⇒t`) is the
work: each of the 105 relations between the cycles and the six gate rules is
derived from r1, …, r7. No other development's theorem or derivation is
used; the derivations were found by the searches of `gen/` and are replayed
by Agda.

*Three wires first* (`BySymmetric`, `Width1`, `Width2`, `Width3`,
`ThreeWire`). On k ≤ 3 wires the circuits are all permutations of the 2ᵏ
states, which `Examples/Groups/Symmetric` presents by the transpositions of
two consecutive points. Along the Gray code that transposition is an *edge
Toffoli*: NOT on the wire that changes, controlled by the other wires. A
Reidemeister–Schreier step from Symmetric's presentation
(`BySymmetric.Step`, the same four facts) needs the Coxeter relations
between the edge Toffolis and each gate as a word in them, derived from the
rules. A proof-producing Knuth–Bendix completion finds those derivations
(`gen/narrow.py`: on three wires 33 targets through 339 rules), and
`Engine`'s `derive` replays them (`Width2/Derivations`, `Width3/Derivations`).
So `complete₃ : ⟦ w ⟧ ≐ ⟦ v ⟧ → 3 T.⊢ w ≈ v`, from r1, …, r6 and the laws of
the swap.

*The steps of a four-wire derivation* (`FourWire`, `Frames`, `Letters`). A
letter on four wires is a gate on the bottom three wires, on the top three,
or both, so a derivation is made of

- `bot l r`, `top l r`: two three-wire circuits with the same function, on
  the bottom or the top three wires, equal by `complete₃`; the evidence is a
  boolean on the eight states;
- rule (7), the naturality of the swap at CCX, and the eleven commutations
  of a gate that touches wire 0 with a gate that touches wire 3: the rule
  instances that involve all four wires;
- `hstep u v`: two words in the NOT gates and swaps with the same function.
  They generate the 384 symmetries of the cube; `Frames.hnorm` brings such a
  word to a normal form, one letter at a time by a table of 28 derived
  entries, and two words with the same normal form are equal;
- `frame p p′ b b′`: a three-wire circuit b in the frame p — b between p
  and its reverse, p a word in the NOT gates and swaps — is the circuit b′
  in the frame p′. This is how a gate anywhere on the four wires, with
  black or white controls, is moved, recoloured and brought next to another:
  it is spelled as a base letter `X`, `CX` or `CCX` in a frame.

*The derivations* (`Four/Part1`–`Part14`, generated: 788 lemmas, 15 607
steps). The search works with *placed gates* — NOT, CNOT and Toffoli in any
placement with black or white controls, 76 in all — and three moves: a
three-wire step, the use of a *pair lemma* (two gates g, h that together
touch all four wires, with (g h)² the identity or a single gate), and its
reverse. Rule (7) is such a lemma, and the pair lemmas fall into 12 orbits
under the symmetries of the cube; a representative of each of the other 11
is derived from the orbits before it, starting with rule (7) alone
(`gen/search/boot.py`). The 105 relations between the cycles fall into 24
shapes under the same symmetries (`gen/shapes.py`), and each cycle is
`(T C)²` for two coloured Toffoli gates in two ways, related by one more
lemma (F). A derivation of each shape and of F was found by best-first
search; the order relation K³ = ε is composed from two lemmas found that way
(`gen/search/order.py`). `gen/four.py` compiles the macro derivations into
the steps above, replaying every one of them, and `gen/inst.py` transports
the 24 shapes to the 105 instances between the words of `Syntactics`.

*The gates* (`gen/search/gates.py`, `gen/gatesc.py`). Four consecutive
positions 2k, …, 2k + 3 are the corners of a square, and the two cycles on
them generate a Klein four-group two of whose elements are Toffoli gates:
`Ω (i + 1) • Ω i` and `Ω (i + 1) • Ω i • Ω i • Ω (i + 1)`. `X`, `CX`, both
directions of CNOT on the wires 1 2 and 2 3, and so the swaps of those
wires, are three-wire words in these; `CCX` is three of them, by one
four-wire step; and the swap of the wires 0 1 is two controlled swaps, each
`Ω i • t • Ω j` for one of those Toffoli gates t. That gives every gate on
its own wires as the circuit of *some* word in the cycles
(`Four/Relations`: `gate-Xᵀ`, …; for the swap of the wires 2 3 the word has
120 letters).

*The equivalence* (`Equivalence`). With the relations between the cycles
derived, g carries Lafont's derivations to derivations from the rules
(`Lemmas.FromCycles`, `gʷ-congᵀ`). A gate's word above and `Translation`'s
have the same permutation — that of the gate — so they are equal by Lafont's
completeness, and the gate rules follow (`to-f`, `lemma-g-fᵀ`). So `s⇒t`,
and with `t⇒s`: `rules≅relations` (`Presentation.MorphismId`),
`Theorem-Rules-iso-Cycles` (the first step for the rules), `presentationᵀ`,
`soundᵀ`, `completeᵀ`, `normal-formᵀ`.

## Modules

| module | contents |
|---|---|
| `Syntactics` | the gates, `K`, the cycles `Ω i`, the translated relation `_SRel,_===_` and `_VRel,_===_` |
| `Translation` | Lafont's cycles `ω₀ … ω₁₃`, the translations `f` and `g` (`gᵈ`) |
| `Semantics` | circuits as functions on bit vectors, `same`, `ax-sound`, `sound` |
| `Numbering` | the Gray-code numbering `enc`, `dec`, and `fin16` |
| `Lemmas` | `FromCycles.lemma-g-rel`, `lemma-X↑`, `lemma-CX↑`, `lemma-CCX↑`, `lemma-g-f` |
| `Bridge` | the semantics of the translations: `f-sem`, `g-sem` |
| `Iso` | the first step: the four facts and `Theorem-Circuits-iso-Cycles` |
| `Presentation` | `⟦_⟧ᴬ`, `presentation`, `sound`, `complete` for the translated relation |
| `NormalForm` | `NF`, `stairs`, `canon`, `nf`, the normal-form theorems |
| `Theory` | the rules r1, …, r7 (`_TRel,_===_`, `module T`), `T-sound`, `t⇒s` |
| `Engine` | equations between letter lists, `rw`, `derive` |
| `BySymmetric` | the Reidemeister–Schreier step from Symmetric's presentation, for any width |
| `Width1`, `Width2`, `Width3` | its instances; `Width2/Derivations`, `Width3/Derivations` generated |
| `ThreeWire` | `complete₁`, …, `presentation₃` |
| `FourWire` | `bot`, `top`, rule (7) and the four-wire rule instances as equations |
| `Frames` | `hstep`, `frame` |
| `Letters` | letter lists as strings; the steps `bo`, `to`, `hs`, `fr`, `rwˢ` |
| `Four/Part1`–`Part14` | the derivations, generated |
| `Four/Relations` | `orderᵀ`, `nearᵀ`, `farᵀ`, `apartᵀ`, `gate-Xᵀ`, …, generated |
| `Equivalence` | the second step: `s⇒t`, `rules≅relations`, `Theorem-Rules-iso-Cycles`, `presentationᵀ` |
| `MainTheorem` | the statements behind one import |

## The generators (`gen/`)

Python 3, no dependencies. Every search is bounded and is run through
`capped.py`, which puts the script in a job with a memory limit and a
timeout:

    python capped.py 1500 600 script.py …      (megabytes, seconds)

| script | what it does |
|---|---|
| `common.py`, `words.py`, `check.py` | the data of the first step: the numbering, K, `omega_circuit(i)`, the six base words; numerical checks |
| `shapes.py` | the 105 instances up to the symmetries of the cube: 24 shapes |
| `narrow.py` → `narrow2.json`, `narrow3.json` | Knuth–Bendix completion of the rules on two and three wires (`Examples/Independence/gen/kb.py`), with a derivation of each Coxeter relation and gate word |
| `mk_narrow.py` | writes `Width2/Derivations.agda`, `Width3/Derivations.agda` |
| `search/macro.py`, `search/pairs.py` | the macro calculus on placed gates; the pair lemmas and their 12 orbits |
| `search/boot.py` → `boot.json` | a representative of each orbit of pair lemmas, from rule (7) alone |
| `search/run_macro.py NAME` → `macro_NAME.json` | best-first search for one relator (a shape, F, L1, Tz) |
| `search/order.py` → `macro_order.json` | K³ = ε composed from L1 and Tz |
| `search/gates.py` → `gates.json` | the macro derivations behind the gates |
| `four.py` | the compiler: placed gates as letters, frames, the steps and their replay |
| `inst.py`, `gatesc.py` | the 105 instances from the shapes; the gates as words in the cycles |
| `mk_four.py`, `mk_rel.py` | write `Four/Part*.agda` and `Four/Relations.agda` |

To regenerate the four-wire layer from the stored derivations (about a
minute): `python capped.py 1500 600 mk_four.py`; `mk_four.py check` compiles
and replays without writing. Every search runs inside those limits:
`boot.py`, `gates.py` and `order.py` take seconds, and a relator from a
fraction of a second to a minute (`search/README.md` has the table, and what
it took to get the last four inside: another form of a cycle for three
shapes, and words stored as bytes for near (0,1)).

## Typechecking

Check `MainTheorem.agda`, which reaches all 38 modules of the folder:

    agda Examples/Groups/Alt16-RevCir/MainTheorem.agda

From scratch it takes about 45 s given the interfaces of `Alternating` and
`Symmetric`, with a peak residency of 0.46 GB; the fourteen generated parts
take about 20 s of that.

Traps met:

- `Surjectivity.canonical 16 a` computes, sixteen levels deep, so two
  spellings of its argument must never meet under it (`nf-sem` exhausted a
  3 GB heap that way). For the same reason every statement about
  permutations is pointwise, and no two closed elements of `Alt 16` are
  compared.
- The evidence of a step that evaluation decides is a hidden argument of
  type `T …` (`Letters`), which Agda solves by eta once the boolean has
  evaluated to `true`; a false step is an unsolved metavariable.
- `_∧_` is not injective for unification: a lemma that takes `a ∧ b ≡ true`
  apart needs a and b given (`Frames`).
- A change of frame `frame p p′ b b′` needs p⁻¹ p′ to keep the top wire in
  place. A CNOT has two idle wires, and the frame that parks the wrong one
  on top is first changed by the top swap, which commutes with the bottom
  CNOT (`gen/four.py`, `to_frame`).
