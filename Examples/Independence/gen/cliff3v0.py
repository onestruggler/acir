"""Paper-V0's rules at p = 3 (Examples.Groups.ProjectiveClifford.Qupit.
Paper-V0.Syntactics), decoded into Cliff₃.

Paper-V0 words are in operator order (the rightmost letter acts first)
over H, S and CZ; Cliff₃'s are in diagram order.  The decoding reverses
a word and reads H and S as themselves and CZ as Cliff₃'s CZ word (CZW,
exact).  A rule u = v of Paper-V0 decodes to an equation of Cliff₃ up to
a power of ω₁₂, which `rules` computes (the rules hold only modulo
scalars in Paper-V0, which erased them)."""
import cmath

import cliff3  # noqa: F401  (the qutrit gates)
from circ import parse, unitary

# CZ |b₀ , b₁⟩ = ω^(b₀ b₁) |b₀ , b₁⟩, in Cliff₃'s gates on wires w, w+1.
CZW = 'Hd0 CX10 H0'


def czw(w):
    return ' '.join(t[:-1] + str(int(t[-1]) + w) if t[-1].isdigit() and not t.startswith('CX')
                    else ('CX%d%d' % (int(t[2]) + w, int(t[3]) + w) if t.startswith('CX') else t)
                    for t in CZW.split())


# Paper-V0 words, operator order: lists of ('H', w), ('S', w), ('CZ', w).
def H(w=0): return [('H', w)]
def S(w=0): return [('S', w)]
def CZ(w=0): return [('CZ', w)]


def pw(word, k):
    return word * k


def up(word):
    return [(g, w + 1) for g, w in word]


Sinv = S() * 2                                  # S ^ (p-1)
Zw = H() + H() + S() + H() + H() + Sinv         # Z = H H S H H S⁻¹
R = S() + Zw * 2                                # R = S Z^½, ½ = 2


def RHR(a, b):
    return R * a + H() + R * b + H() + R * a + H()


XMg = RHR(2, 2)                                 # g = 2, g⁻¹ = 2
M_1 = RHR(2, 2)                                 # M(-1) = RHR (-1) (-1)⁻¹, -1 = 2
XM1 = RHR(1, 1)                                 # XM(1)
Ex = (CZ() + H(0) + H(1)) * 3                   # CZ H↓ H↑, three times
CX = H(0) * 3 + CZ() + H(0)                     # H↓³ CZ H↓
CZ02 = Ex + up(CZ()) + Ex

RULES = [
    ('order-S', 1, S() * 3, []),
    ('order-H', 1, H() * 2, M_1),
    ('M-power-0', 1, [], XM1),
    ('M-power-1', 1, XMg, XMg),
    ('M-power-2', 1, XMg * 2, XM1),
    ('semi-MR', 1, XMg + R, R + XMg),           # R^(g g) = R^1
    ('order-SH', 1, (S() + H()) * 3, []),
    ('comm-HHSHHS', 1, H() + H() + S() + H() + H() + S(), S() + H() + H() + S() + H() + H()),
    ('order-CZ', 2, CZ() * 3, []),
    ('order-Ex', 2, Ex * 2, []),
    ('comm-CZ-S↑', 2, CZ() + up(S()), up(S()) + CZ()),
    ('semi-M↑CZ', 2, up(XMg) + CZ() * 2, CZ() + up(XMg)),
    ('semi-Ex-S↑', 2, Ex + up(S()), S() + Ex),
    ('semi-Ex-H↑', 2, Ex + up(H()), H() + Ex),
    ('blake-c12', 2, up(S()) * 2 + S() * 2 + CX * 2 + S() + CX, CZ()),
    ('yang-baxter', 3, up(Ex) + Ex + up(Ex), Ex + up(Ex) + Ex),
    ('cz-slide', 3, Ex + up(Ex) + CZ(), up(CZ()) + Ex + up(Ex)),
    ('semi-CX↑-CZ↓', 3, CZ() + up(CX), CZ02 + up(CX) + CZ()),
]


def decode(word):
    """Cliff₃ text, diagram order."""
    out = []
    for g, w in reversed(word):
        out.append(czw(w) if g == 'CZ' else '%s%d' % (g, w))
    return ' '.join(out)


def phase(a, b, n):
    """k with ⟦a⟧ = ζᵏ ⟦b⟧, or None."""
    A, B = unitary(parse(a), n), unitary(parse(b), n)
    N = len(A)
    i, j = max(((i, j) for i in range(N) for j in range(N)), key=lambda ij: abs(B[ij[0]][ij[1]]))
    r = A[i][j] / B[i][j]
    for k in range(12):
        z = cmath.exp(1j * cmath.pi * k / 6)
        if abs(r - z) < 1e-9 and all(abs(A[x][y] - z * B[x][y]) < 1e-9 for x in range(N) for y in range(N)):
            return k
    return None


def rules():
    """(name, width, lhs text, rhs text with its phase in front)."""
    out = []
    for name, n, l, r in RULES:
        L, Rr = decode(l), decode(r)
        k = phase(L, Rr, n)
        assert k is not None, name
        out.append((name, n, L, (('w%d ' % k) if k else '') + Rr))
    return out


if __name__ == '__main__':
    import sys
    sys.stdout.reconfigure(encoding='utf-8')
    from circ import same
    pass
    for name, n, L, Rr in rules():
        print('%-14s w%d  %3d = %3d letters   %s' % (name, n, len(parse(L)), len(parse(Rr)),
                                                    Rr.split()[0] if Rr.startswith('w') else ''))
