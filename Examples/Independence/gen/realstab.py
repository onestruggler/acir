"""Makary, Ross and Selinger's relations R1–R16
(Examples.Groups.Real-Clifford.Syntactics), words in operator order, and
the decoding D into RCliff₂: the word reversed (time order), CZ on wires
a, a+1 read as H_a CX(a+1, a) H_a."""
import circ
circ.PRIMITIVE.add('Z')

def h(k): return ('H', k)
def z(k): return ('Z', k)
def cz(k): return ('CZ', k)
M = ('m',)

H, Z, CZ = [h(0)], [z(0)], [cz(0)]
def Hu(k=1): return [h(k)]
def Zu(k=1): return [z(k)]
def CZu(k=1): return [cz(k)]
def HH(k=0): return [h(k), h(k + 1)]

C = {
 'R₁':  ([M, M], []),
 'R₂':  (Z + Z, []),
 'R₃':  (H + H, []),
 'R₄':  ((H + Z) * 4, [M]),
 'R₅':  (CZ + CZ, []),
 'R₆':  (CZ + Zu(), Zu() + CZ),
 'R₇':  (CZ + Z, Z + CZ),
 'R₈':  (CZ + Hu() + Zu() + Hu(), Hu() + Z + Zu() + Hu() + CZ),
 'R₉':  (CZ + H + Z + H, H + Z + Zu() + H + CZ),
 'R₁₀': (CZ + Hu() + CZ + Hu(), Z + Hu() + CZ + Hu() + CZ),
 'R₁₁': (CZ + H + CZ + H, H + Zu() + CZ + H + CZ),
 'R₁₂': (CZ + HH() + CZ + HH() + CZ + H, Hu() + CZ + HH() + CZ + HH() + CZ),
 'R₁₃': (CZ + CZu(), CZu() + CZ),
 'R₁₄': (H + CZ + HH() + CZ + Hu() + CZu() + Hu() + CZ + HH() + CZ + H,
         Hu(2) + CZu() + HH(1) + CZu() + Hu() + CZ + Hu() + CZu() + HH(1) + CZu() + Hu(2)),
 'R₁₅': (CZ + HH(1) + CZu() + HH(1) + CZu() + CZ + HH(1) + CZu() + HH(1) + CZu(),
         CZu() + HH(1) + CZu() + HH(1) + CZ),
 'R₁₆': (CZu() + HH() + CZ + HH() + CZ + CZu() + HH() + CZ + HH() + CZ,
         CZ + HH() + CZ + HH() + CZu()),
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
    """In the transcription notation."""
    out = []
    for g in gs:
        if g[0] == 'm': out.append('m')
        elif g[0] in 'HZ': out.append('%s%d' % g)
        elif g[0] == 'CX': out.append('CX%d%d' % (g[1], g[2]))
    return ' '.join(out)


if __name__ == '__main__':
    import sys
    for k, (l, r) in C.items():
        n = max(ARITY[k], 1)
        ok = circ.same(circ.parse(text(D(l))), circ.parse(text(D(r))), n)
        print(k, 'sound' if ok else 'UNSOUND', '|', text(D(l)), '=', text(D(r)))
