# The alternating group on sixteen points as reversible circuits

The circuits on four wires over NOT (`X`), CNOT (`CX`), Toffoli (`CCX`) and
the swap of two adjacent wires (`Ex`) carry out exactly the even permutations
of the sixteen states of the wires. This folder gives a presentation of
Alt(16) on those generators, obtained by a Reidemeister–Schreier step from
Lafont's presentation of Alt(16) by cycles of three consecutive points
(`Examples/Groups/Alternating`, his Theorem 4), over this repository's
`Word`, `Presentation` and `Circuit` framework, with the swap as the
designated swap of `Circuit/Prop.agda`. `MainTheorem.agda` is the entry
point:

- `circuits≅cycles`: the circuits modulo their rules and Lafont's words in
  the cycles ω₀, …, ω₁₃ modulo his relations are isomorphic groups, by the
  translation `f` of gates into words in the cycles; with it the four facts
  the step consists of, `f-well-defined`, `g-well-defined`,
  `f-left-inv-gen` and `g-left-inv-gen`;
- `presentation : (4 CRel,_===_) IsPresentationOf Alt-group 16`, a circuit
  read as the even permutation `⟦ w ⟧ᴬ` of its word, which permutes the
  positions as the circuit maps the states (`⟦⟧ᴬ-sem`);
- `sound`, `complete`: two circuits are equal by the rules exactly when
  they are the same function on the states;
- the normal form: `normal-form` (every circuit is equal by the rules to
  the canonical circuit `canon (nf w)`), `canon-g` (a canonical circuit is
  the translation of Lafont's canonical form, letter for letter),
  `nf-canon`, `canon-unique` (canonical circuits with the same function are
  the same) and `canon-onto` (every even permutation is carried out by
  one).

Nothing is postulated, and every module is `--cubical-compatible --safe`.

## Conventions

Wire 0 is the bottom wire. `CX` has its control on wire 1 and its target on
wire 0, `CCX` its controls on wires 1 and 2 and its target on wire 0, and
`Ex` swaps the wires 0 and 1; `w ↑` is w one wire up. Words are in diagram
order: `w • v` is w followed by v, on both sides (Lafont's words too).

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

## The Reidemeister–Schreier step

The step relates two presentations over different alphabets, in the manner
of `ProjectiveClifford/Qupit/Paper-V0/Iso.agda`, except that there the two
alphabets coincide and here the generators are translated.

**The generators, in both directions** (`Translation`).

- `g` reads a cycle as a circuit: `g ωᵢ = Ω i`.
- `f` reads a gate as a word in the cycles, the permutation of the sixteen
  positions that the gate carries out. The six gates on their own wires
  have words of 8 (`X`), 4 (`CX`), 6 (`CCX`), 8, 12 and 24 letters (the
  swaps of the wires 0 1, 1 2 and 2 3). A gate on other wires goes to the
  word of that gate between the words of the swaps that carry it there.

**The two relation sets.** Lafont's (`Alternating/Syntactics`, at width 16)
are his three relations ω ω ω = ε, ω ω↑ ω = ω↑ ω↑ and
ω ω↑↑ ω = ω↑↑ ω ω↑ at every position, and the commutation of two cycles
three or more points apart, which is a structural rule of his circuits. The
circuits' (`Syntactics`, on four wires only) are

- those relations read between the circuits Ω i: `order i` (i ≤ 13), `near
  i` (i ≤ 12), `far i` (i ≤ 11) and `apart i j` (i + 3 ≤ j ≤ 13), that is
  14 + 13 + 12 + 66 instances;
- six gate rules `gate-X`, `gate-CX`, `gate-CCX`, `gate-Ex₀`, `gate-Ex₁`,
  `gate-Ex₂`, each saying which word in the Ω i a gate on its own wires is;
- the laws of the swap of `Circuit.Prop` (the swap is an involution and
  natural in every gate) and the structural rules of `Circuit.Base`.

**The two sets are equivalent along the translations** (`Iso`, module
`Theorem`):

    f-well-defined : 4 VRel, w === v → (f ʷ) w ≈₂ (f ʷ) v
    g-well-defined : 16 L.VRel, u === t → (g ʷ) u ≈₁ (g ʷ) t
    f-left-inv-gen : (y : L.Gen 16) → [ y ]ʷ ≈₂ (f ʷ) (g y)
    g-left-inv-gen : (x : Gen 4)    → [ x ]ʷ ≈₁ (g ʷ) (f x)

(`≈₁` the circuits' congruence, `≈₂` Lafont's.) The half towards the
circuits is syntactic (`Lemmas`). Every instance of Lafont's relation, read
through g, is one rule of `Syntactics` (`lemma-g-rel`, by recursion on the
instance with the number of shifts as a parameter). Every gate is the
circuit of its word (`lemma-g-f`): for a gate on its own wires that is its
gate rule, and a gate further up is that gate between swaps, `X ↑ ≈ Ex • X
• Ex`, `CX ↑ ≈ σ⁻[ 2 ] • CX • σ[ 2 ]`, `CCX ↑ ≈ σ⁻[ 3 ] • CCX • σ[ 3 ]`, by
the naturality of the swap. The half towards Lafont's words is semantic. A
word in the cycles permutes the positions as its circuit maps the states,
and conversely (`Bridge.f-sem`, `g-sem`, checked on the twelve gates and
the fourteen cycles by evaluation at the sixteen positions); the circuits'
rules are sound for the functions on states (`Semantics.ax-sound`, the
indexed rules decided for all their indices by one boolean each); and two
words in the cycles with the same permutation are equal by Lafont's
relations, the completeness half of his theorem. So no derivation between
the words of the gates is written out.

**The isomorphism.** `Presentation.Morphism`'s
`StarGroupIsomorphism.isGroupIsomorphism f g …` turns the four facts into
`Theorem-Circuits-iso-Cycles`: `f ʷ` is a group isomorphism from the
circuits modulo their rules onto Lafont's words modulo his. The four facts
are the hypotheses of `Normalization.Reidemeister-Schreier`'s simplified
step in each direction, which give injectivity and surjectivity. That every
gate has an inverse circuit (`grouplike`) is transported along g rather
than proved from the rules.

**The presentation** (`Presentation`) is that isomorphism followed by
Lafont's: `⟦ w ⟧ᴬ` is the even permutation of the word `(f ʷ) w`.
Soundness and completeness for the functions on states follow through
`⟦⟧ᴬ-sem`.

**The normal form** (`NormalForm`). Lafont's canonical form of an even
permutation of n points is a canonical form on the points above the first,
followed by a stairs: a run of cycles ω₀ ω₁ … that brings some point to
position 0, its last cycle doubled when the point is the last one. Read
through g, a stairs at the points from d on is `Ω d • Ω (1 + d) • …`
(`stairs`), and a canonical form is the product of its stairs, the highest
first (`canon`); `canon-g` says this circuit is `(g ʷ)` of Lafont's
canonical form. The normal form of a circuit is Lafont's normal form of its
word, `nf w = nf ((f ʷ) w)`. The theorems come from his Lemmas 6 and 8 and
the presentation, and `nfp′` and `unique-nf` package them as a `NormalForm`
with unique normal forms for the semantics `⟦_⟧ᴬ`. All of it is generic:
Lafont's `nf` works by rewriting, and on the word of a circuit it passes
through millions of letters, so it should not be run. To compute a normal form, read it
off the permutation: `nf-sem : nf w ≡ proj₁ (canonical 16 ⟦ w ⟧ᴬ)`, where
`canonical` (`Alternating/Surjectivity`) recurses on the sixteen points.

## What is found

The presentation is Lafont's, read on circuits: 105 relations between the
fourteen circuits Ω i, and six rules that express the gates on their own
wires through the Ω i. It is stated on four wires only (every rule of
`Syntactics` is a rule between circuits on four wires), and it is not
simplified further: nothing is claimed about which of the rules are
needed, and no rule of a few gates between X, CX and CCX is derived as a
replacement for the long ones. A relation between the Ω i is a relation
between circuits of 12 to 24 gates each, and the rule `gate-Ex₂` has 24
cycles on its right.

The swap laws of `Circuit.Prop` are used essentially. There are six gate
rules for twelve generators: the six gates on other wires (`X` on the wires
1, 2, 3, `CX` on the wires 1 2 and 2 3, `CCX` on the wires 1 2 3) are
reached only through the naturality of the swap, and their words under `f`
are defined to match.

## Modules

| module | contents |
|---|---|
| `Syntactics` | the gates, `K`, the cycles `Ω i`, the rules `_SRel,_===_`, the relation `_VRel,_===_` with the swap laws and the structural rules |
| `Translation` | Lafont's cycles `ω₀ … ω₁₃`, the translations `f` and `g` (`gᵈ`) |
| `Semantics` | circuits as functions on bit vectors, `ax-sound`, `sound` |
| `Numbering` | the Gray-code numbering `enc`, `dec`, and `fin16` |
| `Lemmas` | `lemma-g-rel`, `lemma-X↑`, `lemma-CX↑`, `lemma-CCX↑`, `lemma-g-f` |
| `Bridge` | the semantics of the translations: `f-sem`, `g-sem` |
| `Iso` | the four facts and `Theorem-Circuits-iso-Cycles` |
| `Presentation` | `⟦_⟧ᴬ`, `⟦⟧ᴬ-sem`, `presentation`, `sound`, `complete` |
| `NormalForm` | `NF`, `stairs`, `canon`, `nf`, the normal-form theorems, `nfp′`, `unique-nf` |
| `MainTheorem` | the statements behind one import |

## How the data were found (`gen/`)

Three small Python scripts, with no dependencies.

- `common.py` holds the data in the conventions above: the Gray-code
  numbering, the gates as permutations of the positions, K and its
  conjugates on the six faces, `omega_circuit(i)` (the circuit Ω i: the face
  and the NOT gates read off the states i, i + 1, i + 2), and the six base
  words `BASE`.
- `words.py` finds them. Each cycle of three consecutive positions is a
  conjugate of K by NOT gates and swaps, the automorphisms of the 4-cube,
  and the script lists the shortest conjugators. Each of the gates X, CX,
  CCX and the swaps of the wires 0 1 and 1 2 is a product of permutations
  of a few consecutive positions, and a breadth-first search in the group
  the cycles of those positions generate gives a shortest word for each
  factor. The swap of the wires 2 and 3 moves twelve positions; its word
  removes two inversions with every letter, and a cycle changes the number
  of inversions by at most two, so no word is shorter.
- `check.py` checks numerically what the Agda modules prove: each Ω i is
  the cycle (i i+1 i+2), the 14 + 13 + 12 + 66 instances of the relations
  hold, each of the twelve words has its
  gate's permutation, the three conjugations by swaps, and a cycle read
  back through the gates' words is the cycle.

Run them from `gen/`: `python3 words.py`, `python3 check.py`.

## Typechecking

Check `MainTheorem.agda`, which reaches all ten modules of the folder
(about 940 lines without comments and blank lines):

    agda Examples/Groups/Alt16-RevCir/MainTheorem.agda

From scratch it takes 12 s given the interfaces of `Alternating` and
`Symmetric`, with a peak residency of 0.35 GB.

One trap: `Surjectivity.canonical 16 a` computes, sixteen levels deep, so
two spellings of its argument (`⟦ w ⟧ᴬ` against the permutation of
`(f ʷ) w`, which it unfolds to) must never meet under it. Compared that
way, `nf-sem` exhausted a 3 GB heap; stated first for a variable
permutation, it checks at once. For the same reason every statement about
permutations is pointwise, and no two closed elements of `Alt 16` are
compared.
