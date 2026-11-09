"""Appendix A of the four-bit paper: CX and CCX are involutions modulo T.

Diagram order throughout.  Width 2: x = X1, y = X0, a = CX0,
b = SW0 CX0 SW0, w = x a x, v = y b y.  Width 3: x = X2, c = CCX0,
e = SW0 CCX0 SW0, W = x c x, m = x e x, q = CX0, p = SW0 CX0 SW0,
d = p c p.  Each lemma is a list of waypoints; consecutive waypoints are
joined by one rewrite, or by the search when no equation is named.
"""
import sys
from derive import base_lib, derivation, parse, Lib, BASE

out = []


def lemma(lib, name, arity, wps, depth=3, allow=None, doc=None):
    txt = derivation(lib, name, arity, wps, depth=depth, allow=allow)
    w0 = parse(wps[0]); w1 = parse(wps[-1])
    lib.add(name, arity, w0, w1)
    if doc:
        out.append('-- ' + doc)
    out.append(txt)


# ---------------------------------------------------------------- CNOT
L = base_lib(2)
a, b = 'CX0', 'SW0 CX0 SW0'
lemma(L, 'xaxa⁼', 2, ['X1 CX0 X1 CX0', 'X1 CX0 X1 CX0 X1 X1', 'X1 X0 X1', 'X0'],
      doc='(i) w a = y')
lemma(L, 'ay⁼', 2, ['CX0 X0', 'CX0 X1 CX0 X1 CX0', 'X0 CX0'], doc='(ii) a y = y a')
lemma(L, 'axa⁼', 2, ['CX0 X1 CX0', 'CX0 X1 CX0 X1 X1', 'X0 X1'], doc='(iii) a x a = y x')
lemma(L, 'xσ⁼', 2, ['X1 SW0', 'SW0 SW0 X1 SW0', 'SW0 X0 SW0 SW0', 'SW0 X0'],
      doc='X on wire 1 past the swap')
lemma(L, 'vb⁼', 2, ['X0 SW0 CX0 SW0 X0 SW0 CX0 SW0', 'SW0 X1 CX0 SW0 X0 SW0 CX0 SW0',
                    'SW0 X1 CX0 SW0 SW0 X1 CX0 SW0', 'SW0 X1 CX0 X1 CX0 SW0', 'SW0 X0 SW0',
                    'SW0 SW0 X1', 'X1'], doc="(i') v b = x")
lemma(L, 'byb⁼', 2, ['SW0 CX0 SW0 X0 SW0 CX0 SW0', 'SW0 CX0 SW0 SW0 X1 CX0 SW0',
                     'SW0 CX0 X1 CX0 SW0', 'SW0 X0 X1 SW0', 'SW0 X0 SW0 X0', 'SW0 SW0 X1 X0', 'X1 X0'],
      doc="(iii') b y b = x y")
lemma(L, 'xyba⁼', 2, ['X1 X0 SW0 CX0 SW0 CX0', 'CX0 X1 CX0 SW0 CX0 SW0 CX0', 'CX0 X1 SW0',
                      'CX0 SW0 X0', 'CX0 CX0 SW0 CX0 SW0 CX0 X0', 'CX0 CX0 SW0 CX0 SW0 X0 CX0'],
      doc='x y b a = a a b y a')
lemma(L, 'awy⁼', 2, ['CX0 X1 CX0 X1 X0', 'X0 X0', ''], doc='a w y = ε')
lemma(L, 'xyb⁼', 2, ['X1 X0 SW0 CX0 SW0', 'X1 X0 SW0 CX0 SW0 CX0 X1 CX0 X1 X0',
                     'CX0 CX0 SW0 CX0 SW0 X0 CX0 X1 CX0 X1 X0', 'CX0 CX0 SW0 CX0 SW0 X0'],
      doc='(iv) x y b = a a b y')
lemma(L, 'aabb⁼', 2, ['CX0 CX0 SW0 CX0 SW0 SW0 CX0 SW0', 'CX0 CX0 SW0 CX0 SW0 X0 X0 SW0 CX0 SW0',
                      'X1 X0 SW0 CX0 SW0 X0 SW0 CX0 SW0', 'X1 X0 X1 X0', ''], doc='(v) a a b b = ε')
lemma(L, 'bbaa⁼', 2, ['SW0 CX0 SW0 SW0 CX0 SW0 CX0 CX0', 'SW0 CX0 CX0 SW0 CX0 CX0',
                      'SW0 CX0 CX0 SW0 CX0 SW0 SW0 CX0 SW0 SW0', 'SW0 SW0', ''], doc='b b a a = ε')
lemma(L, 'xvb⁼', 2, ['X1 X0 SW0 CX0 SW0 X0 SW0 CX0 SW0', 'X1 X1', ''], doc='x v b = ε')
lemma(L, 'baab⁼', 2, ['SW0 CX0 SW0 CX0 CX0 SW0 CX0 SW0',
                      'X1 X0 SW0 CX0 SW0 X0 SW0 CX0 SW0 SW0 CX0 SW0 CX0 CX0 SW0 CX0 SW0',
                      'X1 X0 SW0 CX0 SW0 X0 SW0 CX0 SW0', ''], doc='(vi) b a a b = ε')
lemma(L, 'CX²⁼', 2, ['CX0 CX0', 'CX0 SW0 CX0 SW0 CX0 CX0 SW0 CX0 SW0 CX0', 'SW0 SW0', ''],
      doc='The CNOT is an involution.')

cnot = list(out)
out.clear()

# ---------------------------------------------------------------- Toffoli
M = base_lib(3)
M.add('CX²⁼', 2, parse('CX0 CX0'), ())
c, e, p, q = 'CCX0', 'SW0 CCX0 SW0', 'SW0 CX0 SW0', 'CX0'
W, m = 'X2 CCX0 X2', 'X2 SW0 CCX0 SW0 X2'
d = 'SW0 CX0 SW0 CCX0 SW0 CX0 SW0'
lemma(M, 'pp⁼', 3, ['SW0 CX0 SW0 SW0 CX0 SW0', 'SW0 CX0 CX0 SW0', 'SW0 SW0', ''], doc='p p = ε')
lemma(M, 'Wc⁼', 3, ['X2 CCX0 X2 CCX0', 'X2 CCX0 X2 CCX0 X2 X2', 'X2 CX0 X2', 'CX0'], doc='(i) W c = q')
lemma(M, 'cq⁼', 3, ['CCX0 CX0', 'CCX0 X2 CCX0 X2 CCX0', 'CX0 CCX0'], doc='(ii) c q = q c')
lemma(M, 'em⁼', 3, ['SW0 CCX0 SW0 X2 SW0 CCX0 SW0 X2', 'SW0 CCX0 X2 SW0 SW0 CCX0 X2 SW0',
                    'SW0 CCX0 X2 CCX0 X2 SW0', 'SW0 CX0 SW0'], doc='e m = p')
lemma(M, 'me⁼', 3, ['X2 SW0 CCX0 SW0 X2 SW0 CCX0 SW0', 'SW0 X2 CCX0 X2 CCX0 SW0', 'SW0 CX0 SW0'],
      doc='m e = p')
lemma(M, 'pqp⁼', 3, ['SW0 CX0 SW0 CX0 SW0 CX0 SW0', 'SW0 SW0 SW0', 'SW0'], doc='p q p = σ')
lemma(M, 'cec⁼', 3, ['CCX0 SW0 CCX0 SW0 CCX0', 'SW0 SW0 CCX0 SW0 CCX0 SW0 CCX0 SW0 SW0',
                     'SW0 SW0 CX0 SW0 CCX0 SW0 CX0 SW0 SW0',
                     'SW0 CX0 SW0 CX0 SW0 CX0 SW0 SW0 CX0 SW0 CCX0 SW0 CX0 SW0 SW0',
                     'SW0 CX0 SW0 CX0 SW0 CX0 SW0 SW0 CX0 SW0 CCX0 SW0 CX0 SW0 SW0 CX0 SW0 CX0 SW0 CX0 SW0',
                     'SW0 CX0 SW0 CX0 CCX0 SW0 CX0 SW0 SW0 CX0 SW0 CX0 SW0 CX0 SW0',
                     'SW0 CX0 SW0 CX0 CCX0 CX0 SW0 CX0 SW0',
                     'SW0 CX0 SW0 CCX0 CX0 CX0 SW0 CX0 SW0', 'SW0 CX0 SW0 CCX0 SW0 CX0 SW0'],
      doc='(iii) c e c = d')
lemma(M, 'mdm⁼', 3, [d, 'X2 SW0 CCX0 SW0 X2 SW0 CCX0 SW0 CCX0 SW0 CX0 SW0',
                     'X2 SW0 CCX0 SW0 X2 SW0 CCX0 SW0 CCX0 SW0 CCX0 SW0 X2 SW0 CCX0 SW0 X2',
                     'X2 SW0 CCX0 SW0 X2 ' + d + ' X2 SW0 CCX0 SW0 X2'], doc='(iv) d = m d m')
lemma(M, 'dc⁼', 3, [d + ' CCX0', 'CCX0 SW0 CCX0 SW0 CCX0 CCX0', 'SW0 CCX0 SW0 ' + d], doc='(v) d c = e d')
lemma(M, 'em=me⁼', 3, [e + ' ' + m, p, m + ' ' + e], doc='e m = m e')
Lmd = 'SW0 CX0 SW0 CX0 X2 CCX0 X2 SW0 CCX0 SW0'          # p q W e
lemma(M, 'Lmd⁼', 3, [Lmd + ' ' + m + ' ' + d, 'SW0 CX0 SW0 CX0 X2 CCX0 X2 ' + p + ' ' + d,
                     'SW0 CX0 SW0 CX0 X2 CCX0 X2 CCX0 SW0 CX0 SW0',
                     'SW0 CX0 SW0 CX0 CX0 SW0 CX0 SW0', 'SW0 CX0 SW0 SW0 CX0 SW0', ''],
      doc='(p q W e) m d = ε')
lemma(M, 'mc⁼', 3, [m + ' ' + c, Lmd + ' ' + m + ' ' + d + ' ' + m + ' ' + c,
                    Lmd + ' ' + d + ' ' + c, Lmd + ' ' + e + ' ' + d,
                    Lmd + ' ' + e + ' ' + m + ' ' + d + ' ' + m,
                    Lmd + ' ' + m + ' ' + e + ' ' + d + ' ' + m,
                    Lmd + ' ' + m + ' ' + d + ' ' + c + ' ' + m, c + ' ' + m], doc='(vi) m c = c m')
ece = 'SW0 CCX0 SW0 CCX0 SW0 CCX0 SW0'
lemma(M, 'dm⁼', 3, [d + ' ' + m, ece + ' ' + m, 'SW0 CCX0 SW0 CCX0 ' + m + ' SW0 CCX0 SW0',
                    'SW0 CCX0 SW0 ' + m + ' CCX0 SW0 CCX0 SW0', m + ' ' + ece, m + ' ' + d],
      doc='(vii) d m = m d')
Ld = 'SW0 CX0 SW0 CX0 X2 CCX0 X2 SW0 CX0 SW0'           # p q W p
lemma(M, 'Ld⁼', 3, [Ld + ' ' + d, 'SW0 CX0 SW0 CX0 X2 CCX0 X2 CCX0 SW0 CX0 SW0',
                    'SW0 CX0 SW0 CX0 CX0 SW0 CX0 SW0', ''], doc='(p q W p) d = ε')
lemma(M, 'mm⁼', 3, [m + ' ' + m, Ld + ' ' + d + ' ' + m + ' ' + m,
                    Ld + ' ' + m + ' ' + d + ' ' + m, Ld + ' ' + d, ''], doc='(viii) m m = ε')
lemma(M, 'CCX²⁼', 3, ['CCX0 CCX0', 'SW0 SW0 CCX0 SW0 SW0 CCX0 SW0 SW0',
                      'SW0 X2 X2 SW0 CCX0 SW0 SW0 CCX0 SW0 SW0',
                      'SW0 X2 X2 SW0 CCX0 SW0 X2 X2 SW0 CCX0 SW0 SW0',
                      'SW0 X2 X2 SW0 CCX0 SW0 X2 X2 SW0 CCX0 SW0 X2 X2 SW0',
                      'SW0 X2 X2 SW0', 'SW0 SW0', ''], doc='The Toffoli gate is an involution.')

toffoli = list(out)

if __name__ == '__main__':
    with open(sys.argv[1], 'w', encoding='utf-8') as f:
        f.write('\n'.join(cnot) + '\n@@\n' + '\n'.join(toffoli))
    print('ok', len(cnot), len(toffoli))
