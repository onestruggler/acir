"""The paper's circuits as words of letters, and their matrices.

Letters (our numbering, wire 0 is the bottom wire), in time order:
  ('m',)      the scalar -1
  ('H', i)    H on wire i
  ('Z', i)    Z on wire i
  ('C', i)    CZ on the wires i, i+1
The derived gates X = HZH and CXZ (Section 3) and the derived generators
A-E (Definitions 4.2-4.6) are expanded by their definitions, read off the
TeX source like everything else.
"""
import numpy as np

import tex

BS = chr(92)
s2 = 1 / np.sqrt(2)
MH = s2 * np.array([[1, 1], [1, -1]])
MZ = np.diag([1., -1.])
MCZ = np.diag([1., 1., 1., -1.])


def place(M, k, i, n):
    return np.kron(np.kron(np.eye(2 ** (n - i - k)), M), np.eye(2 ** i))


def mat(word, n):
    U = np.eye(2 ** n)
    for a in word:
        if a[0] == 'm':
            U = -U
        elif a[0] == 'H':
            U = place(MH, 1, a[1], n) @ U
        elif a[0] == 'Z':
            U = place(MZ, 1, a[1], n) @ U
        elif a[0] == 'C':
            U = place(MCZ, 2, a[1], n) @ U
        else:
            raise ValueError(a)
    return U


def width(word):
    return max([a[1] + (2 if a[0] == 'C' else 1) for a in word if a[0] != 'm'] + [1])


def same(u, v, n=None):
    if n is None:
        n = max(width(u), width(v))
    return np.allclose(mat(u, n), mat(v, n))


def shift(word, s):
    return [a if a[0] == 'm' else (a[0], a[1] + s) for a in word]


# ------------------------------------------------------------ definitions

def _defs():
    src = tex.source()
    out = {}
    # X = HZH and CXZ, Section 3
    sec = tex.section(src, BS + 'section{Annotated and Typed Circuits}', BS + 'section{Normal Forms')
    for ch in tex.equations(sec):
        if len(ch) >= 2 and len(ch[0][0].gates()) == 1:
            g = ch[0][0].gates()[0]
            if g[0] in ('X', 'CXZ'):
                out[g[0]] = (ch[0][0], ch[1][0])
    # A-E, Definitions 4.2-4.6
    sec = tex.section(src, BS + 'label{def:agates}', BS + 'emph{typed derived generators')
    for ch in tex.equations(sec):
        rhs = ch[-1][0]
        for c, _ in ch[:-1]:
            (g,) = c.gates()
            assert g[0] == 'box'
            out[(g[1], g[2])] = (c, rhs)
    return out


DEFS = None


def expand(gates):
    """Gates of a parsed circuit as letters (time order)."""
    global DEFS
    if DEFS is None:
        DEFS = {}
        raw = _defs()
        # expand the definitions themselves (X inside CXZ? none, but keep general)
        for key, (lhs, rhs) in raw.items():
            DEFS[key] = (lhs, rhs)
    out = []
    for g in gates:
        if g[0] in ('H', 'Z'):
            out.append((g[0], g[1]))
        elif g[0] == 'X':
            lhs, rhs = DEFS['X']
            out += shift(expand(rhs.gates()), g[1] - lhs.gates()[0][1])
        elif g[0] == 'CZ':
            out.append(('C', min(g[1], g[2])))
            assert abs(g[1] - g[2]) == 1
        elif g[0] == 'CXZ':
            # H on the XZ wire, CZ, H on the XZ wire, CZ (Section 3)
            lhs, rhs = DEFS['CXZ']
            (l0,) = lhs.gates()
            assert expand(rhs.gates()) == [('H', l0[1]), ('C', min(l0[1], l0[2])),
                                           ('H', l0[1]), ('C', min(l0[1], l0[2]))]
            assert abs(g[1] - g[2]) == 1
            c = min(g[1], g[2])
            out += [('H', g[1]), ('C', c), ('H', g[1]), ('C', c)]
        elif g[0] == 'box':
            lhs, rhs = DEFS[(g[1], g[2])]
            (l0,) = lhs.gates()
            out += shift(expand(rhs.gates()), g[3][0] - l0[3][0])
        else:
            raise ValueError(g)
    return out


def word(c, neg=False):
    return expand(c.gates()) + ([('m',)] if neg else [])


def typed_relations():
    """The 139 typed relations of Appendix B: (number, figure, lhs, rhs)
    with lhs, rhs parsed circuits and signs."""
    src = tex.source()
    app = tex.section(src, BS + 'section{Typed Relations}', BS + 'section{Proofs of Propositions')
    figs = app.split(BS + 'caption{Rewrite rules for normal forms')
    out = []
    for f, text in enumerate(figs[:-1]):
        for ch in tex.equations(text):
            assert len(ch) == 2
            out.append((len(out) + 1, f + 3, ch[0], ch[1]))
    return out


def reduced_relations():
    """The reduced relations R1-R16 of Figure 1 (relations.tex is input by
    the paper; its circuits are read from the paper source's directory)."""
    import os
    path = os.path.join(os.path.dirname(tex.TEX), 'relations.tex')
    text = open(path, encoding='utf-8').read()
    return tex.equations(text)
