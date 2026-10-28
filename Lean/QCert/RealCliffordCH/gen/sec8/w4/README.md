# Appendix D.3 / D.4 at fixed width (packages (ii), (iii))

Python 3 + numpy; imports the shared scripts of `gen/sec8` (`letters.py`, `mc.py`,
`model.py`, `gen_small.py`) through `sys.path`.

* `tok.py` — the tokens of `Sec8/D/WEng.lean` (`WE.Tk`): `('s', kind, j)` a letter,
  `('g', Kd, tg, cs)` the multi-controlled gate `mc N Kd tg (SE.ctl N cs false)` (`cs`
  sorted by decreasing wire), `('p', m, w, ps)` the `m`-wire letter word `w` placed on
  the wires `ps` by `placeG`.  `letters(N, t)` is the letter word of `Tk.circ N t` on the
  nose; `ok`, `avoids`, `drop`, `relabel`, `swp_ok` and `Engine.apply_step` mirror the
  Lean definitions (the semantic check numerically).
* `conv.py` — parsed gates (figparse) as tokens: every paper gate is one token (a
  coloured two-wire gate is one placed word); checked against `model.py` on all 1924
  diagram instances of D.3 (`testconv.py D3.json`).
* `letters_util.py` — letter words of a token within the span of its wires, and the
  pieces of a four-wire gadget by Definition 2.4 (box with three controls, `ZX`/`XZ` with
  three controls, `H` with two).
* `solve.py` — one paper step (two token words with the same semantics) as engine steps:
  common prefix/suffix; one semantic window (`sem`, any idle wire); splitting into two
  independent changes; aligning a common token by commutations; far commutations of
  tokens on disjoint wires covering every wire (conjugation by a swap network with `swp`,
  then letters exchanged by `sw`); deleting an identity window; rewriting with an earlier
  equation (exact occurrences, both ways, either side); unfolding a four-wire gadget
  (its letters through a `rfl` table entry, the canonical pieces folded into tokens, the
  network distributed by `swp`, the colours by `X X = 1`).  A budget per step and a memo
  of failures keep the search bounded.
* `gen_w4.py D3.json OUT.lean EQ …` — for each equation in order, the chain's steps solved
  and assembled into one run from the statement's token words `LNNN` to `RNNN`, checked
  by the Python engine, written as Lean (`tNNN`); earlier equations enter later tables
  through their `tNNN`.  For the equations that `Small.lean` exports, `eNNN` carries the
  SmallDefs letter words `lNNN`, `rNNN` to the token words (gate by gate: a semantic
  window, or the `rfl` fold of a four-wire gadget).  (161) is proved as the paper does,
  by (150) and Lemma B.4 (`prove161`: the parsed chain has a spurious `= 1` at its
  start).
* `cover.py D3.json [EQ …]` — which paper steps the solver turns into runs (no table).

`D3.json` is `chains.py PAPER.pdf 79 136 D3.json` (about 40 s).  The module
`Sec8/D/W4/A.lean` is `gen_w4.py D3.json A.lean 150 151 152 153 154 155 157 158 159 161
162 163 164 165 166 167 168 169 170 171 172 174 175 176` (equations that fail are left
out and reported; the title line is edited by hand).

## State

Proved (token level, `W4/A.lean`): (150), (151), (154), (155), (157), (158), (159),
(161), (162), (164), (168), (169); exported to `W4.lean`: `d157`, `d168`.
Lean checks `A.lean` in about 2.5 minutes.

Not yet: (152) (its statement and chain ends differ by a reordering the solver does not
find), (153) (cites (152) for `XZ`, i.e. through the inverse of (152): table entries for
inverses and conjugates are the next tactic), (156) and (160) (no chain: "follows
directly from (154), (155)" and "(157), (159)": combine the earlier runs), (163),
(165)–(167), (170)–(176) (each blocked on a cited equation used in a derived form, or on
(152)/(165)), everything from (177) on; the families (Bool parameters, per instance) and
D.4 (`W5.lean`).
