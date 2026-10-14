# The phase gadget at every target, its forms, and the engine's setup.
import deriv
from deriv import Derivation, show, norm, rename_letter
import passes as P
from lemmas8 import L
from lemmas5 import PP3

def perm_for(t, k):
    """a wire map pi with pi(0) = t, sending PP3 to the canonical gadget at
    target t and PP2's single control 2 to k (k != the largest other
    wire), or None when k is that wire."""
    a, b, c = sorted(w for w in range(4) if w != t)
    if k == c: return None
    other = a if k == b else b
    return (t, other, k, c)

def canon(t):
    a, b, c = sorted(w for w in range(4) if w != t)
    return [('TOFF', t, a, b), ('CS', t, c), ('TOFF', t, a, b), ('CSd', t, c)]

def form(t, k):
    o = sorted(w for w in range(4) if w not in (t, k))
    return norm([('TOFF', t, o[0], o[1]), ('CS', t, k), ('TOFF', t, o[0], o[1]), ('CSd', t, k)])

def setup():
    for t in range(4):
        c = canon(t)
        a, b, cc = sorted(w for w in range(4) if w != t)
        # canonical at t: PP3 relabelled by (t, a, b, cc)
        pi0 = (t, a, b, cc)
        name0 = deriv.relabel('S2', pi0, L)          # canon(t) -> form(t, b)
        assert norm(L[name0][0]) == norm(c) and norm(L[name0][1]) == form(t, b), (L[name0], c)
        P.add_form(P.units(c), P.units(form(t, b)), name0)
        pi1 = (t, b, a, cc)
        name1 = deriv.relabel('S2', pi1, L)          # canon(t) (controls a b swapped) -> form(t, a)
        assert norm(L[name1][0]) == norm(c) and norm(L[name1][1]) == form(t, a), (L[name1], c)
        P.add_form(P.units(c), P.units(form(t, a)), name1)
    return {t: P.units(canon(t)) for t in range(4)}
