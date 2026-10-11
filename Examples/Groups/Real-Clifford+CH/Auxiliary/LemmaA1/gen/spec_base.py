import sys, itertools
sys.path.insert(0, '.')
from gen_a1 import chain, alist, parse, letter, idx

# Lemma signatures: name -> (index list whose pairs are the hypotheses, lhs, rhs).
# Axioms of Figure 7 are given with their hypothesis index lists too.
AX = {
    'a2': ('ab', 'axiom (a2 %s)'), 'a3': ('ab', 'axiom (a3 %s)'),
    'c1': ('ab', 'axiom (c1 %s)'), 'd2': ('ab', 'axiom (d2 %s)'),
    'c5': ('abc', 'axiom (c5 %s)'), 'e2*': ('bc', 'axiom (e2* %s)'),
}
LEM = {}   # name -> index list (string)

class Ctx:
    def __init__(self, idxs):
        self.idxs = idxs
    def d(self, x, y):
        if x.isdigit() and y.isdigit():
            assert x != y
            return '(λ ())'
        assert x != y, (x, y)
        if x + y in self.pairs: return x + y
        if y + x in self.pairs: return '(sy %s)' % (y + x)
        raise SystemExit('no evidence for %s %s' % (x, y))
    @property
    def pairs(self):
        return [a + b for a, b in itertools.combinations(self.idxs, 2)]
    def ev(self, names, actual):
        prs = list(itertools.combinations(range(len(names)), 2))
        return ' '.join(self.d(actual[i], actual[j]) for i, j in prs)
    def ax(self, name, *actual):
        names, fmt = AX[name]
        return fmt % self.ev(names, actual)
    def lem(self, name, *actual):
        names = LEM[name]
        e = self.ev(names, actual)
        return '%s %s' % (name, e) if e else name

def sym(p):
    return 'sym (%s)' % p

OUT = []
def lemma(name, idxs, lhs, rhs, steps, comment=None):
    """idxs: the lemma's own indices (variables), in hypothesis order."""
    LEM[name] = idxs
    c = Ctx(idxs)
    st = [(o, n, f(c)) + tuple(rest) for (o, n, f, *rest) in steps]
    out = chain(name, list(idxs), lhs, rhs, st)
    pairs = c.pairs
    hyps = ' → '.join('%s ≢ %s' % (p[0], p[1]) for p in pairs)
    sig = '∀ {%s : Fin N} → %s%s ≈ %s' % (' '.join(idxs), hyps + ' → ' if hyps else '',
                                  ' • '.join(letter(t) for t in parse(lhs)) or 'ε',
                                  ' • '.join(letter(t) for t in parse(rhs)) or 'ε')
    s = ''
    if comment:
        s += ''.join('-- %s\n' % l for l in comment)
    s += '%s : %s\n' % (name, sig)
    s += '%s %s =\n  run {%s}\n      {%s}\n' % (name, ' '.join(['{%s}' % i for i in idxs] + pairs), alist(parse(lhs)), alist(parse(rhs)))
    s += '    ( ' + ''.join('(%s) ▸\n      ' % o for o in out)
    s += 'done)\n\n'
    OUT.append(s)

def alias(name, idxs, sig_l, sig_r, body, comment=None):
    LEM[name] = idxs
    c = Ctx(idxs)
    pairs = c.pairs
    hyps = ' → '.join('%s ≢ %s' % (p[0], p[1]) for p in pairs)
    sig = '∀ {%s : Fin N} → %s%s ≈ %s' % (' '.join(idxs), hyps + ' → ' if hyps else '',
                                  ' • '.join(letter(t) for t in parse(sig_l)),
                                  ' • '.join(letter(t) for t in parse(sig_r)))
    s = ''
    if comment:
        s += ''.join('-- %s\n' % l for l in comment)
    s += '%s : %s\n%s %s = %s\n\n' % (name, sig, name, ' '.join(pairs), body(c))
    OUT.append(s)

A = lambda *a: (lambda c: c.ax(*a))
L = lambda *a: (lambda c: c.lem(*a))
S = lambda f: (lambda c: sym(f(c)))

# --- (e1), (e2) -------------------------------------------------------------
lemma('e1', 'bc', 'Xbc', 'Xcb', [
    ('', 'Xbc Xbc', S(A('a2', 'b', 'c')), 1),
    ('', 'Hbc Hbc', S(A('a3', 'b', 'c')), 1),
    ('Hbc Xbc', 'Zc Hbc', S(A('d2', 'b', 'c'))),
    ('Xbc Hbc', 'Hcb Xbc', S(A('e2*', 'b', 'c'))),
    ('Xbc Zc', 'Zb Xbc', S(A('c1', 'b', 'c'))),
    ('Xbc Hbc', 'Hcb Xbc', S(A('e2*', 'b', 'c'))),
    ('Xbc Xbc', '', A('a2', 'b', 'c')),
    ('Zb Hcb', 'Hcb Xcb', A('d2', 'c', 'b')),
    ('Hcb Hcb', '', A('a3', 'c', 'b')),
], ['(e1): an exchange does not depend on the order of its indices.'])

lemma('e2', 'bc', 'Hcb', 'Xbc Hbc Xbc', [
    ('', 'Xbc Xbc', S(A('a2', 'b', 'c')), 1),
    ('Hcb Xbc', 'Xbc Hbc', A('e2*', 'b', 'c')),
], ['(e2): a Hadamard with its indices exchanged.'])

# --- (c3), (c2), (c4) ------------------------------------------------------
lemma('c3′', 'abc', 'Xbc Xab', 'Xac Xbc', [
    ('', 'Hab Hab', S(A('a3', 'a', 'b')), 1),
    ('Hab Xab', 'Zb Hab', S(A('d2', 'a', 'b'))),
    ('Xbc Hab', 'Hac Xbc', S(A('c5', 'a', 'b', 'c'))),
    ('', 'Xbc Xbc', S(A('a2', 'b', 'c')), 3),
    ('Zb Xbc', 'Xbc Zc', A('c1', 'b', 'c')),
    ('Xbc Xbc', '', A('a2', 'b', 'c')),
    ('Xbc Hab', 'Hac Xbc', S(A('c5', 'a', 'b', 'c'))),
    ('Zc Hac', 'Hac Xac', A('d2', 'a', 'c')),
    ('Hac Hac', '', A('a3', 'a', 'c')),
], ['(c3), read right to left.'])

lemma('c2', 'abc', 'Xab Xac', 'Xbc Xab', [
    ('Xac', 'Xca', L('e1', 'a', 'c')),
    ('Xab Xca', 'Xcb Xab', L('c3′', 'c', 'a', 'b')),
    ('Xcb', 'Xbc', L('e1', 'c', 'b')),
], ['(c2), read right to left.'])

lemma('c4', 'abc', 'Xab Hac', 'Hbc Xab', [
    ('', 'Xca Xca', S(A('a2', 'c', 'a')), 2),
    ('Hac Xca', 'Xca Hca', A('e2*', 'c', 'a')),
    ('Xab Xca', 'Xcb Xab', L('c3′', 'c', 'a', 'b')),
    ('Xab Hca', 'Hcb Xab', S(A('c5', 'c', 'a', 'b'))),
    ('Xab Xca', 'Xcb Xab', L('c3′', 'c', 'a', 'b')),
    ('Xcb Hcb', 'Hbc Xcb', S(A('e2*', 'c', 'b'))),
    ('Xcb Xcb', '', A('a2', 'c', 'b')),
], ['(c4), read right to left.'])

# --- The variants (c2†), (c4†), (c5†) ---------------------------------------
lemma('c2†′', 'abc', 'Xac Xab', 'Xab Xbc', [
    ('', 'Xab Xab', S(A('a2', 'a', 'b')), 0),
    ('Xab Xac', 'Xbc Xab', L('c2', 'a', 'b', 'c'), 1),
    ('Xab Xab', '', A('a2', 'a', 'b'), 2),
], ['(c2†), read right to left.'])

lemma('c4†′', 'abc', 'Hac Xab', 'Xab Hbc', [
    ('', 'Xab Xab', S(A('a2', 'a', 'b')), 0),
    ('Xab Hac', 'Hbc Xab', L('c4', 'a', 'b', 'c')),
    ('Xab Xab', '', A('a2', 'a', 'b')),
], ['(c4†), read right to left.'])

lemma('c5†′', 'abc', 'Hab Xbc', 'Xbc Hac', [
    ('', 'Xbc Xbc', S(A('a2', 'b', 'c')), 0),
    ('Xbc Hab', 'Hac Xbc', S(A('c5', 'a', 'b', 'c'))),
    ('Xbc Xbc', '', A('a2', 'b', 'c')),
], ['(c5†), read right to left.'])

# --- (b2), (b5), (b3) ------------------------------------------------------
lemma('b2', 'abc', 'Zc Xab', 'Xab Zc', [
    ('', 'Xac Xac', S(A('a2', 'a', 'c')), 0),
    ('Xac Zc', 'Za Xac', S(A('c1', 'a', 'c'))),
    ('Xac Xab', 'Xab Xbc', L('c2†′', 'a', 'b', 'c')),
    ('Za Xab', 'Xab Zb', A('c1', 'a', 'b')),
    ('Zb Xbc', 'Xbc Zc', A('c1', 'b', 'c')),
    ('Xab Xbc', 'Xac Xab', S(L('c2†′', 'a', 'b', 'c'))),
    ('Xac Xac', '', A('a2', 'a', 'c')),
], ['(b2): a sign away from an exchange passes it.'])

lemma('b5', 'abcd', 'Hcd Xab', 'Xab Hcd', [
    ('', 'Xac Xac', S(A('a2', 'a', 'c')), 0),
    ('Xac Hcd', 'Had Xac', S(L('c4†′', 'a', 'c', 'd'))),
    ('Xac Xab', 'Xab Xbc', L('c2†′', 'a', 'b', 'c')),
    ('Had Xab', 'Xab Hbd', L('c4†′', 'a', 'b', 'd')),
    ('Hbd Xbc', 'Xbc Hcd', L('c4†′', 'b', 'c', 'd')),
    ('Xab Xbc', 'Xac Xab', S(L('c2†′', 'a', 'b', 'c'))),
    ('Xac Xac', '', A('a2', 'a', 'c')),
], ['(b5): an exchange and a Hadamard on disjoint pairs commute.'])

lemma('b3', 'abcd', 'Xcd Xab', 'Xab Xcd', [
    ('', 'Xac Xac', S(A('a2', 'a', 'c')), 0),
    ('Xac Xcd', 'Xad Xac', S(L('c2†′', 'a', 'c', 'd'))),
    ('Xac Xab', 'Xab Xbc', L('c2†′', 'a', 'b', 'c')),
    ('Xad Xab', 'Xab Xbd', L('c2†′', 'a', 'b', 'd')),
    ('Xbd Xbc', 'Xbc Xcd', L('c2†′', 'b', 'c', 'd')),
    ('Xab Xbc', 'Xac Xab', S(L('c2†′', 'a', 'b', 'c'))),
    ('Xac Xac', '', A('a2', 'a', 'c')),
], ['(b3): exchanges on disjoint pairs commute.'])

# --- Conjugation by an exchange renames ------------------------------------
cancel = lambda c, x, y: c.ax('a2', x, y)
lemma('rX-xy', 'xy', 'Xxy Xxy Xxy', 'Xyx', [
    ('Xxy Xxy', '', A('a2', 'x', 'y'), 0),
    ('Xxy', 'Xyx', L('e1', 'x', 'y')),
], ['Conjugating a letter by X_[x,y] exchanges x and y in it.'])
lemma('rX-yx', 'xy', 'Xxy Xyx Xxy', 'Xxy', [
    ('Xyx', 'Xxy', L('e1', 'y', 'x')),
    ('Xxy Xxy', '', A('a2', 'x', 'y'), 0),
])
lemma('rX-xo', 'xyb', 'Xxy Xxb Xxy', 'Xyb', [
    ('Xxy Xxb', 'Xyb Xxy', L('c2', 'x', 'y', 'b')),
    ('Xxy Xxy', '', A('a2', 'x', 'y')),
])
lemma('rX-yo', 'xyb', 'Xxy Xyb Xxy', 'Xxb', [
    ('Xxy', 'Xyx', L('e1', 'x', 'y'), 0),
    ('Xxy', 'Xyx', L('e1', 'x', 'y'), 2),
    ('Xyx Xyb', 'Xxb Xyx', L('c2', 'y', 'x', 'b')),
    ('Xyx Xyx', '', A('a2', 'y', 'x')),
])
lemma('rX-ox', 'xya', 'Xxy Xax Xxy', 'Xay', [
    ('Xax', 'Xxa', L('e1', 'a', 'x')),
    ('Xxy Xxa', 'Xya Xxy', L('c2', 'x', 'y', 'a')),
    ('Xxy Xxy', '', A('a2', 'x', 'y')),
    ('Xya', 'Xay', L('e1', 'y', 'a')),
])
lemma('rX-oy', 'xya', 'Xxy Xay Xxy', 'Xax', [
    ('Xxy', 'Xyx', L('e1', 'x', 'y'), 0),
    ('Xay', 'Xya', L('e1', 'a', 'y')),
    ('Xxy', 'Xyx', L('e1', 'x', 'y'), 2),
    ('Xyx Xya', 'Xxa Xyx', L('c2', 'y', 'x', 'a')),
    ('Xyx Xyx', '', A('a2', 'y', 'x')),
    ('Xxa', 'Xax', L('e1', 'x', 'a')),
])
lemma('rX-oo', 'xyab', 'Xxy Xab Xxy', 'Xab', [
    ('Xxy Xab', 'Xab Xxy', L('b3', 'a', 'b', 'x', 'y')),
    ('Xxy Xxy', '', A('a2', 'x', 'y')),
])
lemma('rH-xy', 'xy', 'Xxy Hxy Xxy', 'Hyx', [
    ('Xxy Hxy Xxy', 'Hyx', S(L('e2', 'x', 'y'))),
])
lemma('rH-yx', 'xy', 'Xxy Hyx Xxy', 'Hxy', [
    ('Hyx', 'Xxy Hxy Xxy', L('e2', 'x', 'y')),
    ('Xxy Xxy', '', A('a2', 'x', 'y'), 0),
    ('Xxy Xxy', '', A('a2', 'x', 'y'), 1),
])
lemma('rH-xo', 'xyb', 'Xxy Hxb Xxy', 'Hyb', [
    ('Xxy Hxb', 'Hyb Xxy', L('c4', 'x', 'y', 'b')),
    ('Xxy Xxy', '', A('a2', 'x', 'y')),
])
lemma('rH-yo', 'xyb', 'Xxy Hyb Xxy', 'Hxb', [
    ('Xxy', 'Xyx', L('e1', 'x', 'y'), 0),
    ('Xxy', 'Xyx', L('e1', 'x', 'y'), 2),
    ('Xyx Hyb', 'Hxb Xyx', L('c4', 'y', 'x', 'b')),
    ('Xyx Xyx', '', A('a2', 'y', 'x')),
])
lemma('rH-ox', 'xya', 'Xxy Hax Xxy', 'Hay', [
    ('Xxy', 'Xyx', L('e1', 'x', 'y'), 0),
    ('Xxy', 'Xyx', L('e1', 'x', 'y'), 2),
    ('Xyx Hax', 'Hay Xyx', S(L('c5†′', 'a', 'y', 'x'))),
    ('Xyx Xyx', '', A('a2', 'y', 'x')),
])
lemma('rH-oy', 'xya', 'Xxy Hay Xxy', 'Hax', [
    ('Xxy Hay', 'Hax Xxy', S(L('c5†′', 'a', 'x', 'y'))),
    ('Xxy Xxy', '', A('a2', 'x', 'y')),
])
lemma('rH-oo', 'xyab', 'Xxy Hab Xxy', 'Hab', [
    ('Xxy Hab', 'Hab Xxy', S(L('b5', 'x', 'y', 'a', 'b'))),
    ('Xxy Xxy', '', A('a2', 'x', 'y')),
])
lemma('rZ-x', 'xy', 'Xxy Zx Xxy', 'Zy', [
    ('Zx Xxy', 'Xxy Zy', A('c1', 'x', 'y')),
    ('Xxy Xxy', '', A('a2', 'x', 'y')),
])
lemma('rZ-y', 'xy', 'Xxy Zy Xxy', 'Zx', [
    ('Xxy', 'Xyx', L('e1', 'x', 'y'), 0),
    ('Xxy', 'Xyx', L('e1', 'x', 'y'), 2),
    ('Zy Xyx', 'Xyx Zx', A('c1', 'y', 'x')),
    ('Xyx Xyx', '', A('a2', 'y', 'x')),
])
lemma('rZ-o', 'xya', 'Xxy Za Xxy', 'Za', [
    ('Xxy Za', 'Za Xxy', S(L('b2', 'x', 'y', 'a'))),
    ('Xxy Xxy', '', A('a2', 'x', 'y')),
])

if __name__ == '__main__':
    print(''.join(OUT))
