# Deriving Lafont's relations from r1..r7: feasibility of derivation search

Python only. The scripts here import `../common.py` and, read-only,
`XCXCCX-4bit/gen/pg_search.py` and its `pg_results.json`.

## Verdict

Derivations exist and were found for **all 24 shapes** (order; near (0,1),
(1,2); far (0,2,1), (1,3,2); all 19 apart shapes), plus a form-change lemma F
that the symmetry argument needs.

They are derivations in a *macro calculus*, not flat lists of rule (7) steps:

- three-wire ("narrow") steps, and
- uses of **12 pair lemmas**: four-wire equations between at most five gates,
  one per orbit under the symmetries of the 4-cube.

Each of the 12 pair lemmas is itself derived from rule (7) and three-wire
steps (2 to 202 steps), by composing the equations E1..E8 that
`XCXCCX-4bit/gen/pg_results.json` has (and `XCXCCX-4bit/Equations4.agda`
proves).

What is checked and what is not:

- **Macro derivations:** each is replayed by two independent checkers
  (`macro.check`, and `verify_all.py` with its own gate semantics and trace
  test). Every step preserves the permutation of the 16 states, every narrow
  step stays on three wires, every lemma step is a true equation of the stated
  shape.
- **Pair lemmas:** each derivation is replayed by `pg_search.check_derivation`
  and by a second checker in `pairlemmas_raw.py`.
- **Not done:** the macro derivations were not expanded into flat rule (7) +
  three-wire step lists; the raw counts below are computed from the lemma
  costs, not replayed. Transport of a pair lemma from its orbit representative
  to the instance used (wire relabelling, X-conjugation) is argued, not
  executed.

## The calculus

Letters are coloured placed gates: X, CX and Toffoli in any placement with
black or white controls, 76 in all. Names read `0~2>1` = target 1, black
control 0, white control 2. Words are in diagram order, up to interchange of
letters on disjoint wires.

| step | meaning |
|---|---|
| `narrow` | a block on at most 3 wires is replaced by a shortest word with the same function |
| `pair` | adjacent g, h spanning four wires with (g h)² = k, k the identity or one gate: `g h → h g k` or `k h g` |
| `expand` | a gate k → `g h g h` for such a pair |

There are 2496 ordered pairs of this kind, in 12 orbits under wire
permutations and X on wires (`pairs.py`). One representative of each is
derived in `pairlemmas_raw.py`:

| | pair | statement | raw steps (narrow + rule7) | from |
|---|---|---|---|---|
| P01 | `1>0 , 23>0` | CX and Toffoli, same target: commute | 7 (5+2) | E4 |
| P02 | `1>0 , 23>1` | (P c)² = Q | 2 (1+1) | rule (7) |
| P03 | `1>0 , 03>2` | CX onto a control: (a P)² = `13>2` | 157 (126+31) | E1, E3 |
| P04 | `1>0 , 13>2` | CX from a control: commute | 7 (5+2) | E5 |
| P05 | `1>0 , ~13>2` | the same, opposite colours | 9 (7+2) | E5 |
| P06 | `12>0 , 13>0` | same target, one common control: commute | 77 (61+16) | E3 |
| P07 | `12>0 , ~13>0` | the same, opposite colours | 86 (68+18) | E3, E4 |
| P08 | `12>0 , 23>1` | target of one a control of the other: (P g)² = `23>0` | 33 (24+9) | E7 |
| P09 | `12>0 , ~23>1` | the same, opposite colours: commute | 202 (160+42) | E7, E1, E5, E3 |
| P10 | `12>0 , 12>3` | same controls: commute | 7 (5+2) | E2 |
| P11 | `12>0 , 1~2>3` | the same, one colour opposite | 16 (12+4) | E2, E5 |
| P12 | `12>0 , ~1~2>3` | the same, both opposite | 23 (17+6) | E2, E5 |

### Symmetries assumed, and why they are derivable

- **Wire permutations.** A relabelled derivation is a derivation; rule (7) is
  used in all 24 relabellings. In Agda this is naturality of the swap.
- **Polarity (X on any set of wires).** Conjugate a derivation by X on wire w,
  letter by letter: a narrow step stays a narrow step on the same triple; a
  rule (7) step `P c P = Q c` with w a control of P and Q costs one extra
  narrow step; with w the control of c it costs two. So at most 3 extra narrow
  steps per rule (7) step, and no extra rule (7) steps.
- **Forms of a pair lemma.** `g h → k h g`, `g h → h g k`, `k → g h g h` and
  the other orientation all follow from `g h g h = k` by inserting and
  cancelling pairs `x x` (narrow steps) and one use of the lemma.

## Results

Representatives are those `shapes.py` prints. "Letters" is the length of the
relator `lhs rhs⁻¹` that is reduced to the empty word. Raw figures: the rule
(7) count is exact given the lemma costs; the narrow count lies between "lemma
costs only" and "plus 3 per rule (7) step and 12 per lemma use".

| equation | letters | macro steps (narrow + pair + expand) | raw rule7 | raw narrow | search: expansions, time |
|---|---|---|---|---|---|
| **order** K³ = id | 12 | 77 (58+9+10) | 544 | 2257–4117 | composed, see below |
| near (0,1) | 20 | 123 (74+23+26) | 1256 | 5058–9414 | 10100, 55.5 s † |
| near (1,2) | 20 | 70 (39+22+9) | 718 | 2730–5256 | 102, 0.8 s |
| far (0,2,1) | 24 | 94 (57+23+14) | 736 | 2877–5529 | 595, 5.1 s |
| far (1,3,2) | 24 | 110 (63+27+20) | 1056 | 4078–7810 | 3616, 54.4 s |
| apart (0,3) | 16 | 29 (14+13+2) | 326 | 1200–2358 | 58, 0.4 s |
| apart (0,4) | 16 | 73 (42+19+12) | 662 | 2663–5021 | 6823, 38.5 s † |
| apart (0,5) | 16 | 84 (50+19+15) | 922 | 3780–6954 | 231, 1.3 s |
| apart (0,6) | 16 | 53 (26+21+6) | 786 | 3070–5752 | 485, 2.6 s |
| apart (0,7) | 16 | 35 (19+12+4) | 262 | 943–1921 | 36, 0.3 s |
| apart (0,8) | 16 | 27 (19+6+2) | 248 | 1027–1867 | 18, 0.1 s |
| apart (0,9) | 16 | 22 (12+8+2) | 228 | 910–1714 | 13, 0.1 s |
| apart (0,10) ‡ | 16 | 25 (11+13+1) | 454 | 1752–3282 | 41, 0.2 s |
| apart (0,11) | 16 | 24 (11+12+1) | 446 | 1726–3220 | 25, 0.2 s |
| apart (1,5) | 16 | 39 (24+10+5) | 362 | 1441–2707 | 1988, 11.9 s |
| apart (1,6) | 16 | 86 (52+21+13) | 854 | 3364–6334 | 3214, 24.6 s |
| apart (1,7) | 16 | 25 (11+13+1) | 454 | 1752–3282 | 35, 0.4 s |
| apart (1,8) | 16 | 22 (12+8+2) | 228 | 910–1714 | 14, 0.2 s |
| apart (1,10) | 16 | 22 (9+12+1) | 446 | 1724–3218 | 23, 0.2 s |
| apart (1,11) | 16 | 41 (22+15+4) | 290 | 1033–2131 | 81, 1.0 s |
| apart (2,6) | 16 | 83 (42+31+10) | 874 | 3338–6452 | 11152, 218 s † |
| apart (2,7) | 16 | 27 (13+13+1) | 338 | 1273–2455 | 329, 4.5 s |
| apart (3,6) | 16 | 84 (42+33+9) | 990 | 3849–7323 | 4045, 35.2 s |
| apart (3,7) | 16 | 86 (52+21+13) | 830 | 3235–6133 | 13582, 279 s † |
| F (two forms of K) | 8 | 17 (12+1+4) | 140 | 577–1057 | 11, 0.0 s |
| L1 (piece of order) | 10 | 27 (18+4+5) | 264 | 1087–1987 | 3388, 29.1 s |
| Tz (piece of order) | 12 | 5 (4+1+0) | 16 | 65–125 | 1, 0.0 s |
| C′ (not used) | 8 | 35 (20+9+6) | 392 | 1605–2961 | 12861, 199 s † |

† **Beyond the caps.** Only F, apart (0,10) and the composed order were
produced after the caps (1500 MB, 600 s, through `../capped.py`) were imposed;
everything else comes from earlier uncapped runs. The † entries are the ones
the bounded search cannot reproduce: their runs stored roughly 1.7 to 3.6
million words. Near (0,1), rerun under the caps, stopped at its
1.2-million-word limit after 4576 expansions and 21 s with no derivation
(`rerun_near0_1.json`). The derivations themselves are valid and verified.

‡ **Forms for apart (0,10).** This derivation is in the forms
`Syntactics.agda` uses (form 1 of both cycles). In form 0 of both, an uncapped
run was cut at about 325 s and 14000 expansions without a derivation.

The raw counts are large because the search was not told what lemmas cost:
across all files P03 (157 raw steps) is used 275 times and P09 (202) 97 times.
In Agda the lemmas are used by name, so the macro counts are the relevant
size: **1378 macro steps for the 24 shapes and F**, about 590 of them lemma
uses.

### Order, by thought

Direct search failed on K³ (`pg_search.solve` with E1..E8 as library: nothing
in 804 s; the macro best-first search: nothing after 40000 expansions and 10
million stored words, uncapped). It works when split. Write K = (T C)²,
T = `02>1`, C = `13>0`, t = CX(0→1), z = C t C t C (a three-wire word on wires
0, 1, 3).

- **L1**: `T C T C T = t C T C t` (27 macro steps, found by search).
- **Tz**: `T z = z T` (5 steps).
- Then K³ = (TCTCT) C (TCTCT) C = t C T z T C t C = t C z T T C t C, which is
  a three-wire word equal to the identity.

`verify_all.py` composes this into `macro_order.json`: 77 steps, passed by
both checkers.

### The forms of a cycle, and lemma F

Each cycle Ω_i is (T C)² for coloured Toffolis T, C in exactly two ways: the
two wires it does not move can be given to T and C either way round.
`Syntactics.agda`'s Ω_i is form 1 for all fourteen i. The searches used form 0
throughout, except apart (0,10).

A cube symmetry carrying one instance to another in its orbit may exchange the
two forms of a cycle. So **one derivation per shape is enough only with F**:
`(02>1 13>0)² = (03>1 12>0)²`, i.e. K is invariant under the exchange of wires
2 and 3. F has a 17-step macro derivation.

### A schema for apart?

Partly.

- **10 of the 19 apart shapes are letterwise** (`letterwise.py`): for suitable
  forms, every Toffoli of one cycle commutes with every Toffoli of the other,
  each commutation being three-wire or one of P06, P07, P09. These are (0,3),
  (0,7), (0,8), (0,9), (0,10), (0,11), (1,6), (1,7), (1,8), (1,10).
- **The other 9 are not letterwise in any forms**: (0,4), (0,5), (0,6), (1,5),
  (1,11), (2,6), (2,7), (3,6), (3,7). Their derivations use expand steps and
  were found one by one (27 to 86 macro steps). No uniform argument was found.

A control functor ("a three-wire equation holds under a control") would give
order, near and far at once. It does not exist as stated: the controlled
Toffoli is an odd permutation of the 16 states.

## Files

| file | what it is |
|---|---|
| `kdefs.py` | shared definitions; the cycles as placed-gate words |
| `macro.py` | the calculus: gates, narrow tables, the 2496 pair lemmas, `check`, bounded best-first `search` |
| `run_macro.py` | one target per run → `macro_NAME.json` |
| `pairs.py`, `pairs.json` | the 12 orbits of pair lemmas |
| `pairlemmas_raw.py`, `pairlemmas_raw.json` | the 12 representatives derived from rule (7) + narrow steps |
| `verify_all.py`, `summary_macro.json` | independent re-check of every `macro_*.json`, composition of order, forms, letterwise table |
| `letterwise.py` | which apart instances are letterwise |
| `macro_*.json` | 28 complete, verified macro derivations reducing `relator` to the empty word |
| `rerun_near0_1.json` | the capped rerun that hit the state limit |
| `run_target.py`, `log_order.txt`, `out_order.json` | the failed `pg_search` attempt on order |
| `mlog_*.txt` | logs of the searches run before the caps |

Run any script through the cap: `python ..\capped.py 1500 600 verify_all.py`.

## Open

- Flat expansion of the macro derivations into rule (7) + narrow steps.
- Shorter derivations: the search ignores lemma cost and nothing was polished.
- A search that stays inside the caps on the four † shapes.
- A uniform argument for the 9 non-letterwise apart shapes.
- The six gate rules (each gate as a word in the cycles) were not attempted.
