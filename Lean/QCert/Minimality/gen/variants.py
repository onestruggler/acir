"""Derived forms of an equation, with mechanical derivations: its inverse (both sides
inverted, letter by letter) and, on two wires, its mirror image (upside down)."""
from tsearch import op

def inverse_steps(eng, e, L, R):
    """Steps from inv(L) to inv(R) given the equation e: L = R (operator lists)."""
    iL = eng.inv_word(L); iR = eng.inv_word(R)
    if iL is None or iR is None: return None
    steps = []; cur = list(iL)
    q = len(cur)
    for x in R:                                   # insert R ++ inv(R) at the end
        ex, k = eng.cancel_eq[x]; steps.append(('rw', q, ex, True)); cur[q:q] = [x] * k; q += 1
    assert tuple(cur[len(iL):len(iL) + len(R)]) == tuple(R)
    steps.append(('rw', len(iL), e, True)); cur[len(iL):len(iL) + len(R)] = list(L)
    pos = len(iL)
    for x in L:                                   # cancel inv(L) ++ L from the inside
        ex, k = eng.cancel_eq[x]; pos -= (k - 1)
        assert tuple(cur[pos:pos + k]) == (x,) * k
        steps.append(('rw', pos, ex, False)); del cur[pos:pos + k]
    assert tuple(cur) == tuple(iR)
    return steps

def mirror_letter(a, fr=None):
    g, o = a
    if g == 'SW' or (fr is not None and g in fr.scalars) or (fr is None and g == 'w'): return [a]
    if g == 'CX': return [('SW', 0), ('CX', 0), ('SW', 0)]
    if fr is not None and fr.arity[g] != 1: raise KeyError(g)
    return [(g, 1 - o)]

def mirror_word(w, fr=None):
    out = []
    for a in w: out += mirror_letter(a, fr)
    return tuple(out)

def mirror_push(eng, w, nat1, invol, fr=None):
    """Steps from mirror(w) to [SW] ++ w ++ [SW] (operator lists, two wires)."""
    cur = list(mirror_word(w, fr))
    steps = [('rw', 0, invol, True)]; cur[0:0] = [('SW', 0), ('SW', 0)]
    i = 1
    for x in w:
        g, o = x
        if (fr is not None and g in fr.scalars) or (fr is None and g == 'w'):
            steps.append(('swap', i)); cur[i], cur[i + 1] = cur[i + 1], cur[i]
        elif g == 'SW':
            pass
        elif g == 'CX':
            assert cur[i:i + 4] == [('SW', 0), ('SW', 0), ('CX', 0), ('SW', 0)]
            steps.append(('rw', i, invol, False)); del cur[i:i + 2]
        elif o == 0:
            assert cur[i:i + 2] == [('SW', 0), (g, 1)]
            steps.append(('rw', i, nat1[g], False)); cur[i:i + 2] = [(g, 0), ('SW', 0)]
        else:
            assert cur[i:i + 2] == [('SW', 0), (g, 0)]
            steps.append(('rw', i + 2, invol, True)); cur[i + 2:i + 2] = [('SW', 0), ('SW', 0)]
            steps.append(('rw', i + 1, nat1[g], True)); cur[i + 1:i + 3] = [('SW', 0), (g, 1)]
            steps.append(('rw', i, invol, False)); del cur[i:i + 2]
        i += 1
    assert tuple(cur) == (('SW', 0),) + tuple(w) + (('SW', 0),), (cur, w)
    return steps

def mirror_steps(eng, e, L, R, nat1, invol, fr=None):
    """Steps from mirror(L) to mirror(R) given e: L = R on two wires."""
    from tsearch2 import invert
    sl = mirror_push(eng, L, nat1, invol, fr)
    sr = mirror_push(eng, R, nat1, invol, fr)
    return sl + [('rw', 1, e, False)] + invert(sr)

# --- three wires: conjugation by the reversal R = σ₀ σ₁ σ₀
R3 = (('SW', 0), ('SW', 1), ('SW', 0))

def rho3_letter(a, fr=None):
    g, o = a
    if (fr is not None and g in fr.scalars) or (fr is None and g == 'w'): return [a]
    if g == 'SW': return [('SW', 1 - o)]
    if g == 'CX':
        t = 1 - o                     # CX at o: control o+1, target o -> control 1-o, target 2-o
        return [('SW', t), ('CX', t), ('SW', t)]
    if fr is not None and fr.arity[g] != 1: raise KeyError(g)
    return [(g, 2 - o)]

def rho3_word(w, fr=None):
    out = []
    for a in w: out += rho3_letter(a, fr)
    return tuple(out)

def rconj_push(w, letter_eq, invol, fr=None):
    """Steps from R ++ w ++ R to rho(w) (operator lists, three wires), given letter_eq[x]:
    R x R = rho(x) and invol[o]: σ_o σ_o = ε."""
    cur = list(R3) + list(w) + list(R3)
    steps = []
    p = 0                                   # cur[p:p+3] = R, then a letter, then ...
    for j, x in enumerate(w):
        if j < len(w) - 1:
            q = p + 3 + 1                   # after R x
            steps.append(('rw', q, invol[0], True)); cur[q:q] = [('SW', 0), ('SW', 0)]
            steps.append(('rw', q + 1, invol[1], True)); cur[q + 1:q + 1] = [('SW', 1), ('SW', 1)]
            steps.append(('rw', q + 2, invol[0], True)); cur[q + 2:q + 2] = [('SW', 0), ('SW', 0)]
        assert tuple(cur[p:p + 7]) == R3 + (x,) + R3, (cur[p:p + 7], x)
        steps.append(('rw', p, letter_eq[x], False))
        rx = rho3_letter(x, fr)
        cur[p:p + 7] = rx
        p += len(rx)
    assert tuple(cur) == rho3_word(w, fr)
    return steps
