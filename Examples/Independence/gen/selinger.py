"""Selinger's relations C1–C15 (Examples.Groups.Qubit-Clifford.Syntactics),
words in operator order, and the decoding D into Cliff₂: the word
reversed (time order), CZ on wires a, a+1 read as H_a CX(a+1, a) H_a."""

def h(k): return ('H', k)
def s(k): return ('S', k)
def cz(k): return ('CZ', k)
W = ('w',)

def up(g, k=1):
    if g[0] == 'w': return g
    return (g[0], g[1] + k)

def U(ws, k=1): return [up(g, k) for g in ws]

H, S, CZ = [h(0)], [s(0)], [cz(0)]
def Hu(k=1): return [h(k)]
def Su(k=1): return [s(k)]
def CZu(k=1): return [cz(k)]

C = {
 'C₁':  ([W] * 8, []),
 'C₂':  (H + H, []),
 'C₃':  (S * 4, []),
 'C₄':  (S + H + S + H + S + H, [W]),
 'C₅':  (CZ + CZ, []),
 'C₆':  (CZ + Su(), Su() + CZ),
 'C₇':  (CZ + S, S + CZ),
 'C₈':  (CZ + Hu() + Su() + Su() + Hu(), Hu() + Su() + Su() + Hu() + S + S + CZ),
 'C₉':  (CZ + H + S + S + H, H + S + S + H + Su() + Su() + CZ),
 'C₁₀': (CZ + Hu() + CZ, [W] * 7 + Su() + Hu() + Su() + S + CZ + Hu() + Su()),
 'C₁₁': (CZ + H + CZ, [W] * 7 + S + H + S + Su() + CZ + H + S),
 'C₁₂': (CZ + CZu(), CZu() + CZ),
 'C₁₃': (CZu() + Hu() + Hu(2) + CZu() + H + Hu() + CZ + H + Hu() + CZu() + Hu() + Hu(2) + CZu(),
         CZ + Hu() + H + CZ + Hu(2) + Hu() + CZu() + Hu(2) + Hu() + CZ + Hu() + H + CZ),
 'C₁₄': (CZ + Hu(2) + Hu() + CZu() + Hu() + Hu(2) + CZu() + CZ + Hu() + Hu(2) + CZu() +
         Hu() + Hu(2) + CZu() + CZ + Hu() + Hu(2) + CZu() + Hu() + Hu(2) + CZu(), []),
 'C₁₅': (CZu() + H + Hu() + CZ + Hu() + H + CZ + CZu() + Hu() + H + CZ +
         Hu() + H + CZ + CZu() + Hu() + H + CZ + Hu() + H + CZ, []),
}

ARITY = {'C₁': 0, 'C₂': 1, 'C₃': 1, 'C₄': 1, 'C₅': 2, 'C₆': 2, 'C₇': 2, 'C₈': 2,
         'C₉': 2, 'C₁₀': 2, 'C₁₁': 2, 'C₁₂': 3, 'C₁₃': 3, 'C₁₄': 3, 'C₁₅': 3}


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
        if g[0] == 'w': out.append('w')
        elif g[0] in 'HS': out.append('%s%d' % g)
        elif g[0] == 'CX': out.append('CX%d%d' % (g[1], g[2]))
    return ' '.join(out)
