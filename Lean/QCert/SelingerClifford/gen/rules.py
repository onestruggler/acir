"""Derivations of the supplement's equations 3.1-3.101 (the rewrite rules
of Figures 3-7 of Selinger's paper), translated from the supplement's own
proofs line by line: each labelled step becomes one rewrite found by
`engine.try_step` among the equations its label names, "inv" becomes
`engine.solve_inv`, and "def"/"omega" steps are equalities of words up to
commuting letters."""
from engine import (LABEL, Deriv, canon, reorder_to, solve_inv, strip_w,
                    try_step)
from supp import frame_size, line_word, parse_supp


def derive_eq(eq):
    """(Deriv, None) for the equation, or (None, error)."""
    k = frame_size(eq)
    (lt, lp), (rt, rp) = eq['stmt']
    L = line_word(lt, lp, k)
    R = line_word(rt, rp, k)
    d = Deriv(L, k)
    prev = L
    for idx, (lab, toks, ph) in enumerate(eq['proof']):
        nxt = line_word(toks, ph, k)
        if idx == 0:
            # the first proof line repeats the statement
            prev = nxt
            reorder_to(d, nxt)
            continue
        reorder_to(d, prev)
        if lab in ('def', 'omega'):
            pass
        elif lab == 'inv':
            if not solve_inv(d, nxt):
                return None, f'inv failed at line {idx}'
        else:
            if lab not in LABEL:
                return None, f'unknown label {lab}'
            if not try_step(d, LABEL[lab], nxt):
                return None, f'step {idx} ({lab}) not found'
        a, ap = strip_w(d.word)
        b, bp = strip_w(nxt)
        if canon(a) != canon(b) or (ap - bp) % 8:
            return None, f'mismatch after step {idx} ({lab})'
        d.reduce_phase()
        prev = nxt
    reorder_to(d, R)
    return d, None


def derive_all(log=print):
    """{name: (frame size, steps)} for every equation of the supplement."""
    out = {}
    for eq in parse_supp():
        d, err = derive_eq(eq)
        if err:
            raise RuntimeError(f"equation {eq['name']}: {err}")
        out[eq['name']] = (frame_size(eq), d.steps)
        log(f"rule {eq['name']}: {len(d.steps)} steps")
    return out
