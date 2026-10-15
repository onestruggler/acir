# The relabelling and recolouring tables of the four-wire transport
# (Four/Transport): for each adjacent swap and each letter that is not a
# swap or a scalar, the letter conjugated by the swap is the renamed
# letter; X letters commute and square to the empty word; a swap squares
# to the empty word.  Each is a derivation of deriv.py, lowered and
# emitted like the others, and named so that the Agda side can find it.
import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from deriv import Derivation, rename_letter, norm
from passes import L

SW = [('SWAP', 0, 1), ('SWAP', 1, 2), ('SWAP', 2, 3)]

def letters():
    out = []
    for w in range(4):
        for k in ('S', 'Sd', 'K', 'Kd', 'X', 'Z'): out.append((k, w))
    for a in range(4):
        for b in range(4):
            if a == b: continue
            if a < b: out += [('CS', a, b), ('CSd', a, b), ('CZ', a, b)]
            out += [('CX', a, b), ('CK', a, b), ('CKd', a, b)]
    for s in ((0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)): out.append(('CCZ',) + s)
    for t in range(4):
        cs = [w for w in range(4) if w != t]
        for i in range(3):
            for j in range(i + 1, 3): out.append(('TOFF', t, cs[i], cs[j]))
    return out

def tau(j):
    p = {w: w for w in range(4)}; p[j], p[j + 1] = j + 1, j
    return p

def sw_name(j, g): return f'sw{j} ' + g[0] + ''.join(str(w) for w in g[1:])

def make():
    names = []
    for j in range(3):
        for g in letters():
            name = sw_name(j, g)
            if name in L: names.append(name); continue
            d = Derivation(name, [SW[j], g, SW[j]], [rename_letter(g, tau(j))], L)
            d.swapconj(0, 1, j)
            d.done(); names.append(name)
    for a in range(4):
        name = f'xx{a}'
        if name not in L:
            d = Derivation(name, [('X', a), ('X', a)], [], L); d.win(0, 2, []); d.done()
        for b in range(4):
            if a == b: continue
            name = f'xc{a}{b}'
            if name not in L:
                d = Derivation(name, [('X', a), ('X', b)], [('X', b), ('X', a)], L); d.comm(0); d.done()
    for j in range(3):
        name = f'swsw{j}'
        if name not in L:
            d = Derivation(name, [SW[j], SW[j]], [], L); d.win(0, 2, []); d.done()
    make_x()
    return names

# ------------------------------------------------------------ X lists
BITS = [tuple((m >> w) & 1 for w in range(4)) for m in range(16)]

def xb(bits): return [('X', w) for w in range(4) if bits[w]]
def bstr(bits): return ''.join(str(b) for b in bits)
def tog(bits, w): return tuple(b ^ (1 if v == w else 0) for v, b in enumerate(bits))
def pb(bits, j):
    t = tau(j); out = [0] * 4
    for w in range(4):
        if bits[w]: out[t[w]] = 1
    return tuple(out)

def sort_xs_der(d, k, have, want):
    """bubble X letters at k .. into the order want; cancel adjacent equal pairs first."""
    cur = list(have)
    changed = True
    while changed:
        changed = False
        for i in range(len(cur) - 1):
            if cur[i] == cur[i + 1]:
                d.win(k + i, k + i + 2, []); del cur[i:i + 2]; changed = True; break
        if changed: continue
        for i in range(len(cur) - 1):
            if cur[i][1] > cur[i + 1][1]:
                d.comm(k + i); cur[i], cur[i + 1] = cur[i + 1], cur[i]; changed = True; break
    assert cur == want, (cur, want)

def make_x():
    for w in range(4):
        for bits in BITS:
            for side in ('t', 's'):
                name = f'x{side}{w} {bstr(bits)}'
                if name in L: continue
                lhs = ([('X', w)] + xb(bits)) if side == 't' else (xb(bits) + [('X', w)])
                rhs = xb(tog(bits, w))
                d = Derivation(name, lhs, rhs, L)
                sort_xs_der(d, 0, lhs, rhs); d.done()
    for j in range(3):
        for bits in BITS:
            name = f'xr{j} {bstr(bits)}'
            if name in L: continue
            lhs = [rename_letter(g, tau(j)) for g in xb(bits)]
            rhs = xb(pb(bits, j))
            d = Derivation(name, lhs, rhs, L)
            sort_xs_der(d, 0, lhs, rhs); d.done()
