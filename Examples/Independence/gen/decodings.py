"""G.1 of Blake's paper: Selinger's relations, decoded, derived in Cliff₂.

The decoding D reads a word of Selinger's (operator order) backwards
and spells CZ on wires a, a+1 as H_a CX(a+1, a) H_a (selinger.py), so
that each decoded relation is a drawing of the paper's in time order.
Every one but (C4) and (C12) is its cited lemma of Appendix A up to
commuting letters; (C12) is (A.25) backwards, and (C4) is (H S)³ = ω
where the paper draws (S H)³.  The decoding of the swap, needed for the
encoding of σ, is (A.16)'s argument.

Each equation is stated on the decoded letters exactly, so that the
Agda decoding function produces its sides."""
from appendixA import D, LIB, OUT
import cliff
from selinger import C, ARITY, D as decode, text

first = len(OUT)

CITE = {'C₅': 'A18⁼', 'C₆': 'A19⁼', 'C₇': 'A20⁼', 'C₈': 'A21⁼', 'C₉': 'A22⁼',
        'C₁₀': 'A23⁼', 'C₁₁': 'A24⁼', 'C₁₂': 'A25⁼', 'C₁₃': 'A26⁼', 'C₁₄': 'A27⁼',
        'C₁₅': 'A28⁼'}
NAME = {k: 'D' + k + '⁼' for k in C}

D(NAME['C₁'], 0, [(text(decode(C['C₁'][0])), None), ('', ['w8'])], mirror=False)
D(NAME['C₂'], 1, [(text(decode(C['C₂'][0])), None), ('', ['H2'])], mirror=False)
D(NAME['C₃'], 1, [(text(decode(C['C₃'][0])), None), ('', ['S4'])], mirror=False)
D(NAME['C₄'], 1, [(text(decode(C['C₄'][0])), None),
                  ('w Sd0 H0 Sd0 S0 H0 S0', ['E']),
                  ('w Sd0 H0 H0 S0', ['S4']),
                  ('w Sd0 S0', ['H2']),
                  (text(decode(C['C₄'][1])), ['S4'])], mirror=False)
for k, lemma in CITE.items():
    l, r = C[k]
    D(NAME[k], ARITY[k], [(text(decode(l)), None), (text(decode(r)), [lemma])], mirror=False)

# CNOT: H CZ H on the target, decoded, is CNOT.
D('DCX⁼', 2, [('H0 H0 CX10 H0 H0', None), ('CX10', ['H2'])], mirror=False)

# The swap: H0 CZ H0 · H1 CZ H1 · H0 CZ H0, decoded, is σ.
D('Dσ⁼', 2, [('H0 H0 CX10 H0 H0 H1 H0 CX10 H0 H1 H0 H0 CX10 H0 H0', None),
             ('CX10 H1 H0 CX10 H0 H1 CX10', ['H2']),
             ('CX10 CX01 CX10', ['A9⁼', 'H2']),
             ('SW01 CX10 CX10', ['B']),
             ('SW01', ['A5⁼'])], mirror=False)

# Only the new equations go into the module.
del OUT[:first]
