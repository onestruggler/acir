# The searches behind the four-wire derivations

Python 3, no dependencies; nothing here reads another development. Every
script is bounded (a limit on stored words and on time) and is run through
the cap of `../capped.py`, one at a time:

    python ..\capped.py 1500 600 SCRIPT.py …        (megabytes, seconds)

The results are macro derivations, kept as JSON. `../four.py` compiles them
into the steps of `FourWire.agda` and `Frames.agda`, replaying every step,
and `../mk_four.py` writes them as `Four/Part*.agda`, where Agda checks them
again.

## The calculus (`macro.py`)

Letters are *placed gates*: NOT, CNOT and Toffoli in any placement on the
four wires, with black or white controls, 76 in all. `0~2>1` is the Toffoli
gate with target 1, a black control on wire 0 and a white control on wire 2.
Words are in diagram order, up to the interchange of letters on disjoint
wires. A derivation reduces a relator `lhs rhs⁻¹` to the empty word by

| step | meaning |
|---|---|
| `narrow` | a block on at most three wires is replaced by a shortest word with the same function |
| `pair` | adjacent g, h that together touch all four wires, with (g h)² = k, k the identity or one gate: `g h → h g k` or `k h g` |
| `expand` | a gate k → `g h g h` for such a pair |

A narrow step is a three-wire fact, which the rules decide (`ThreeWire`). A
pair or expand step uses a *pair lemma*, (g h)² = k. There are 2496 ordered
pairs of this kind, in 12 orbits under the symmetries of the cube — the
permutations of the wires and NOT on any of them (`pairs.py`).

## The pair lemmas (`boot.py` → `boot.json`)

One orbit is rule (7): with T = `23>1`, c = `1>0`, Q = `23>0` it says
T c T = Q c, that is (T c)² = Q. `boot.py` starts with that orbit alone and
searches for a representative of each other orbit in the calculus restricted
to the orbits known so far, adding an orbit as soon as its representative is
derived. All eleven are found, in 20 s in all:

| pair | statement | macro steps |
|---|---|---|
| `1>0 , 23>0` | CX and Toffoli, same target: commute | 7 |
| `1>0 , 13>2` | CX from a control: commute | 6 |
| `1>0 , ~13>2` | the same, the control white | 7 |
| `12>0 , 13>0` | same target, one common control: commute | 54 |
| `12>0 , ~13>0` | the same, opposite colours | 8 |
| `12>0 , 23>1` | target of one a control of the other: (g h)² = `23>0` | 21 |
| `12>0 , ~23>1` | the same, opposite colours: commute | 12 |
| `12>0 , 12>3` | same controls: commute | 6 |
| `12>0 , 1~2>3` | the same, one colour opposite | 6 |
| `12>0 , ~1~2>3` | the same, both opposite | 9 |
| `1>0 , 03>2` | CX onto a control: (g h)² = `13>2` | 7 |

The last one fails while only rule (7) and the first orbit are known, and is
found at once after the others.

## The relators (`run_macro.py NAME` → `macro_NAME.json`)

Each cycle Ω_i is (T C)² for two coloured Toffoli gates in exactly two ways:
the two wires it does not move can be given to T and C either way round
(`../inst.py`, `FORMS`). Lafont's 105 instances fall into 24 shapes under
the symmetries of the cube (`../shapes.py`): order 1, near 2, far 2, apart
19. One relator per shape is searched for, with the full table of pair
lemmas, by best-first search on the length of the word; the name gives the
cycles and, after `_f`, the forms used when they are not both form 0.

| relator | letters | macro steps | expansions, time |
|---|---|---|---|
| order (9) | 12 | 77 | composed, see below |
| near (0,1) | 20 | 123 | 10100, 47 s |
| near (1,2) | 20 | 70 | 102, 0.8 s |
| far (0,2,1) | 24 | 94 | 595, 5 s |
| far (1,3,2) | 24 | 110 | 3616, 54 s |
| apart (0,3) | 16 | 29 | 58, 0.4 s |
| apart (0,4), forms 0 1 | 16 | 85 | 892, 5 s |
| apart (0,5) | 16 | 84 | 231, 1.3 s |
| apart (0,6) | 16 | 53 | 485, 2.6 s |
| apart (0,7) | 16 | 35 | 36, 0.3 s |
| apart (0,8) | 16 | 27 | 18, 0.1 s |
| apart (0,9) | 16 | 22 | 13, 0.1 s |
| apart (0,10), forms 1 1 | 16 | 25 | 41, 0.2 s |
| apart (0,11) | 16 | 24 | 25, 0.2 s |
| apart (1,5) | 16 | 39 | 1988, 12 s |
| apart (1,6) | 16 | 86 | 3214, 25 s |
| apart (1,7) | 16 | 25 | 35, 0.4 s |
| apart (1,8) | 16 | 22 | 14, 0.2 s |
| apart (1,10) | 16 | 22 | 23, 0.2 s |
| apart (1,11) | 16 | 41 | 81, 1 s |
| apart (2,6), forms 1 0 | 16 | 25 | 39, 0.2 s |
| apart (2,7) | 16 | 27 | 329, 4.5 s |
| apart (3,6) | 16 | 84 | 4045, 35 s |
| apart (3,7), forms 1 0 | 16 | 25 | 19, 0.1 s |
| F (the two forms of K) | 8 | 17 | 11, 0 s |
| L1 (piece of order) | 10 | 27 | 3388, 29 s |
| Tz (piece of order) | 12 | 5 | 1, 0 s |

Two things made the difference between a search that runs out of room and
one that ends in a second:

- **The forms.** In form 0 of both cycles, apart (0,4), (2,6) and (3,7)
  were found only by runs that stored two to four million words; with one
  cycle in its other form each is found within a thousand expansions. A
  shape is a statement about permutations, and the relator is one of four
  spellings of it; lemma F relates them afterwards.
- **Storing words as bytes.** A stored word costs about 320 bytes that way
  (it was 500 as a tuple), so near (0,1), whose search stores millions of
  words before it ends, fits in the 1500 MB; with 1.2 million words allowed
  it had stopped short.

**Order** (`order.py` → `macro_order.json`). A direct search does not find
K³ = id. With K = (T C)², T = `02>1`, C = `13>0`, t = CX from wire 0 to
wire 1 and z = C t C t C (a word on the wires 0 1 3):

- L1: `T C T C T = t C T C t`;
- Tz: `T z = z T`;
- so K³ = (T C T C T) C (T C T C T) C = t C T z T C t C = t C z T T C t C,
  a three-wire word equal to the identity.

`order.py` writes that out as one macro derivation (77 steps).

## The gates (`gates.py` → `gates.json`)

Four consecutive positions 2k, …, 2k + 3 are the corners of a square of the
cube, and the two cycles on them generate a Klein four-group, two of whose
elements are Toffoli gates:

    D_i   Ω_{i+1} Ω_i = t_i               (i even)
    V_i   Ω_i Ω_{i+1} = t_i t'_i

Every gate but the bottom swap is a three-wire word in the t_i and t'_i, and
CCX = t_4 t_6 t_8 by one more four-wire step. The swap of the wires 0 1 is
two controlled swaps, Ω_1 t_2 Ω_4 and Ω_9 t_10 Ω_12 (FKa, FKb). The
seventeen relators (9 to 12 letters, 3 to 27 macro steps each) are found in
under a second.

## Files

| file | what it is |
|---|---|
| `macro.py` | the calculus: gates, narrow tables, the pair lemmas, `check`, the bounded best-first `search` |
| `pairs.py` | the 12 orbits of pair lemmas |
| `boot.py`, `boot.json` | the pair lemmas from rule (7) |
| `run_macro.py`, `macro_*.json` | one relator per run |
| `order.py`, `macro_order.json` | the order relation, composed |
| `gates.py`, `gates.json` | the relators behind the gates |

## Not done

- No uniform argument for the relations between the cycles: ten of the
  nineteen apart shapes commute Toffoli gate by Toffoli gate in suitable
  forms, and the others, like near and far, were found one by one. A control
  functor (a three-wire equation holds under a control) would give order,
  near and far at once, but the controlled Toffoli gate is an odd
  permutation of the sixteen states, so it does not exist as stated.
- The derivations are what the search found first; nothing was shortened.
