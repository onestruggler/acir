"""Makary, Ross and Selinger's relations R1–R16 (Examples.Groups.Real-
Clifford.Syntactics), words in operator order, and the decoding into
RCliff₂: the word reversed, CZ on wires a, a+1 read as H_a CX(a+1, a) H_a."""

def h(k): return ('H', k)
def z(k): return ('Z', k)
def cz(k): return ('CZ', k)
M = ('m',)

def U(ws, k=1):
    return [g if g[0] == 'm' else (g[0], g[1] + k) for g in ws]

H, Z, CZ = [h(0)], [z(0)], [cz(0)]
HH = [h(0), h(1)]

R = {
 'R₁':  ([M, M], []),
 'R₂':  (Z + Z, []),
 'R₃':  (H + H, []),
 'R₄':  ((H + Z) * 4, [M]),
 'R₅':  (CZ + CZ, []),
 'R₆':  (CZ + U(Z), U(Z) + CZ),
 'R₇':  (CZ + Z, Z + CZ),
 'R₈':  (CZ + U(H) + U(Z) + U(H), U(H) + Z + U(Z) + U(H) + CZ),
 'R₉':  (CZ + H + Z + H, H + Z + U(Z) + H + CZ),
 'R₁₀': (CZ + U(H) + CZ + U(H), Z + U(H) + CZ + U(H) + CZ),
 'R₁₁': (CZ + H + CZ + H, H + U(Z) + CZ + H + CZ),
 'R₁₂': (CZ + HH + CZ + HH + CZ + H, U(H) + CZ + HH + CZ + HH + CZ),
 'R₁₃': (CZ + U(CZ), U(CZ) + CZ),
 'R₁₄': (H + CZ + HH + CZ + U(H) + U(CZ) + U(H) + CZ + HH + CZ + H,
         U(H, 2) + U(CZ) + U(HH) + U(CZ) + U(H) + CZ + U(H) + U(CZ) + U(HH) + U(CZ) + U(H, 2)),
 'R₁₅': (CZ + U(HH) + U(CZ) + U(HH) + U(CZ) + CZ + U(HH) + U(CZ) + U(HH) + U(CZ),
         U(CZ) + U(HH) + U(CZ) + U(HH) + CZ),
 'R₁₆': (U(CZ) + HH + CZ + HH + CZ + U(CZ) + HH + CZ + HH + CZ,
         CZ + HH + CZ + HH + U(CZ)),
}

ARITY = {'R₁': 0, 'R₂': 1, 'R₃': 1, 'R₄': 1, 'R₅': 2, 'R₆': 2, 'R₇': 2, 'R₈': 2,
         'R₉': 2, 'R₁₀': 2, 'R₁₁': 2, 'R₁₂': 2, 'R₁₃': 3, 'R₁₄': 3, 'R₁₅': 3, 'R₁₆': 3}


def D(word):
    out = []
    for g in reversed(word):
        if g[0] == 'CZ':
            a = g[1]
            out += [('H', a), ('CX', a + 1, a), ('H', a)]
        else:
            out.append(g)
    return out


def text(gs):
    out = []
    for g in gs:
        if g[0] == 'm': out.append('m')
        elif g[0] in 'HZ': out.append('%s%d' % g)
        elif g[0] == 'CX': out.append('CX%d%d' % (g[1], g[2]))
    return ' '.join(out)
