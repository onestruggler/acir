"""The twelve pair lemmas of the macro calculus (pairs.py: one per orbit under
the symmetries of the 4-cube), each derived from rule (7) and three-wire
(narrow) steps, in the step format of XCXCCX-4bit/gen/pg_search.py.

    python ..\\capped.py 1000 300 pairlemmas_raw.py     -> pairlemmas_raw.json

Statement of a lemma for a pair g, h: (g h)^2 = k, written `g h g h = k`
(k one gate), or g h = h g when k is the identity.  White controls are
X before and after.  The derivations are composed by hand from rule (7)
and the equations E1..E8 of XCXCCX-4bit (pg_results.json: themselves
derivations from rule (7) and narrow steps, inlined here), so every
emitted derivation consists of narrow and rule7 steps only.  Each is
checked twice: pg_search.check_derivation and the checker below (own gate
semantics, own trace test, own reading of rule (7)).
"""
import json
import sys

from kdefs import pg, load_library
from pg_search import parse, canon, func, show

sys.dont_write_bytecode = True


class Builder:
    def __init__(self, lib, start):
        self.lib = lib
        self.lin = bytes(start)
        self.start = bytes(start)
        self.steps = []

    def relin(self, new):
        new = bytes(new)
        assert canon(new) == canon(self.lin), 'relin'
        self.lin = new

    def narrow(self, old, new):
        """Replace the first occurrence of the block `old` by `new`."""
        old, new = bytes(old), bytes(new)
        i = self.lin.find(old) if old else 0
        assert i >= 0, 'narrow: block not found: %s in %s' % (show(old), show(self.lin))
        return self.narrow_at(i, i + len(old), new)

    def narrow_at(self, i, j, new):
        new = bytes(new)
        old = self.lin[i:j]
        tis = [ti for ti in range(4) if not any(pg.WM[l] & ~pg.TM[ti] for l in old + new)]
        assert tis, 'narrow: not on a triple'
        assert func(old) == func(new), 'narrow: %s /= %s' % (show(old), show(new))
        self.steps.append(('narrow', tis[0], self.lin, i, j, new))
        self.lin = self.lin[:i] + new + self.lin[j:]

    def lemma(self, old, new):
        """Rewrite the block `old` into `new` by rule (7) or an equation of
        the library, in any relabelling and either direction."""
        old, new = bytes(old), bytes(new)
        i = self.lin.find(old)
        assert i >= 0, 'lemma: block not found: %s in %s' % (show(old), show(self.lin))
        pre, post = self.lin[:i], self.lin[i + len(old):]
        for pi in pg.PERMS:
            l7, r7 = pg.r7_sides(pi)
            for d, (P, Q) in (('fwd', (l7, r7)), ('bwd', (r7, l7))):
                if P == old and Q == new:
                    self.steps.append(('rule7', pi, d, self.lin, i))
                    self.lin = pre + new + post
                    return 'rule7'
        for lid in range(len(self.lib.items)):
            for sigma in pg.PERMS:
                for d in ('fwd', 'bwd'):
                    P, Q = self.lib.sides(lid, sigma, d)
                    if canon(P) == canon(old) and canon(Q) == canon(new):
                        for st in self.lib.derivation(lid, sigma, d):
                            self.steps.append(pg.step_shift(st, pre, post))
                        self.lin = pre + new + post
                        return self.lib.items[lid][0]
        raise AssertionError('no lemma for %s = %s' % (show(old), show(new)))


def build(lib):
    """name -> (macro pair, lhs, rhs, builder)"""
    out = {}

    def lem(name, pair, lhs, rhs, script):
        b = Builder(lib, parse(lhs))
        used = []
        for op in script:
            if op[0] == 'n':
                b.narrow(parse(op[1]), parse(op[2]))
            elif op[0] == 'i':           # insert op[2] after the block op[1]
                at = b.lin.find(parse(op[1])) + len(parse(op[1]))
                assert at >= len(parse(op[1]))
                b.narrow_at(at, at, parse(op[2]))
            elif op[0] == 'l':
                used.append(b.lemma(parse(op[1]), parse(op[2])))
            else:
                b.relin(parse(op[1]))
        assert canon(b.lin) == canon(parse(rhs)), '%s: ends at %s' % (name, show(b.lin))
        out[name] = (pair, parse(lhs), parse(rhs), b, used)

    # 1  CX and a Toffoli with the same target commute (E4)
    lem('P01', '1>0 , 23>0', 'CX1>0 CCX32>0', 'CCX32>0 CX1>0',
        [('l', 'CX1>0 CCX32>0', 'CCX32>0 CX1>0')])
    # 2  rule (7): the Toffoli's target is the CX's control
    lem('P02', '1>0 , 23>1', 'CCX32>1 CX1>0 CCX32>1 CX1>0', 'CCX32>0',
        [('l', 'CCX32>1 CX1>0 CCX32>1', 'CCX32>0 CX1>0'),
         ('n', 'CX1>0 CX1>0', '')])
    # 3  the CX's target is a control of the Toffoli (E1, then E3)
    lem('P03', '1>0 , 03>2', 'CX1>0 CCX30>2 CX1>0 CCX30>2', 'CCX31>2',
        [('l', 'CX1>0 CCX30>2 CX1>0', 'CCX30>2 CCX31>2'),
         ('l', 'CCX31>2 CCX30>2', 'CCX30>2 CCX31>2'),
         ('n', 'CCX30>2 CCX30>2', '')])
    # 4  the CX's control is a control of the Toffoli (E5)
    lem('P04', '1>0 , 13>2', 'CX1>0 CCX31>2', 'CCX31>2 CX1>0',
        [('l', 'CX1>0 CCX31>2', 'CCX31>2 CX1>0')])
    # 5  the same with opposite colours on the shared control
    lem('P05', '1>0 , ~13>2', 'CX1>0 X1 CCX31>2 X1', 'X1 CCX31>2 X1 CX1>0',
        [('n', 'CX1>0 X1', 'X1 CX1>0 X0'),
         ('r', 'X1 CX1>0 CCX31>2 X0 X1'),
         ('l', 'CX1>0 CCX31>2', 'CCX31>2 CX1>0'),
         ('n', 'CX1>0 X0 X1', 'X1 CX1>0')])
    # 6  two Toffolis with the same target and one common control (E3)
    lem('P06', '12>0 , 13>0', 'CCX21>0 CCX31>0', 'CCX31>0 CCX21>0',
        [('l', 'CCX21>0 CCX31>0', 'CCX31>0 CCX21>0')])
    # 7  the same with opposite colours on the common control (E3, E8)
    lem('P07', '12>0 , ~13>0', 'CCX21>0 X1 CCX31>0 X1', 'X1 CCX31>0 X1 CCX21>0',
        [('n', 'X1 CCX31>0 X1', 'CCX31>0 CX3>0'),
         ('l', 'CCX21>0 CCX31>0', 'CCX31>0 CCX21>0'),
         ('l', 'CCX21>0 CX3>0', 'CX3>0 CCX21>0'),
         ('n', 'CCX31>0 CX3>0', 'X1 CCX31>0 X1')])
    # 8  the target of one Toffoli is a control of the other (E7)
    lem('P08', '12>0 , 23>1', 'CCX32>1 CCX21>0 CCX32>1 CCX21>0', 'CCX32>0',
        [('l', 'CCX32>1 CCX21>0 CCX32>1 CCX21>0', 'CCX32>0')])
    # 9  the same with opposite colours on the common control: they commute
    lem('P09', '12>0 , ~23>1', 'CCX21>0 X2 CCX32>1 X2', 'X2 CCX32>1 X2 CCX21>0',
        [('n', 'X2 CCX32>1 X2', 'CCX32>1 CX3>1'),
         ('i', '', 'CCX32>1 CCX32>1'),
         ('i', 'CCX32>1 CCX32>1 CCX21>0 CCX32>1', 'CCX21>0 CCX21>0'),
         ('l', 'CCX32>1 CCX21>0 CCX32>1 CCX21>0', 'CCX32>0'),
         ('i', 'CCX32>1 CCX32>0', 'CX3>1 CX3>1'),
         ('l', 'CX3>1 CCX21>0 CX3>1', 'CCX21>0 CCX32>0'),
         ('l', 'CCX32>0 CX3>1', 'CX3>1 CCX32>0'),
         ('l', 'CCX32>0 CCX21>0', 'CCX21>0 CCX32>0'),
         ('n', 'CCX32>0 CCX32>0', ''),
         ('n', 'CCX32>1 CX3>1', 'X2 CCX32>1 X2')])
    # 10 two Toffolis with the same controls (E2)
    lem('P10', '12>0 , 12>3', 'CCX21>0 CCX21>3', 'CCX21>3 CCX21>0',
        [('l', 'CCX21>0 CCX21>3', 'CCX21>3 CCX21>0')])
    # 11 the same, one control of opposite colours (E2, E5)
    lem('P11', '12>0 , 1~2>3', 'CCX21>0 X2 CCX21>3 X2', 'X2 CCX21>3 X2 CCX21>0',
        [('n', 'X2 CCX21>3 X2', 'CCX21>3 CX1>3'),
         ('l', 'CCX21>0 CCX21>3', 'CCX21>3 CCX21>0'),
         ('l', 'CCX21>0 CX1>3', 'CX1>3 CCX21>0'),
         ('n', 'CCX21>3 CX1>3', 'X2 CCX21>3 X2')])
    # 12 the same, both controls of opposite colours (E2, E5 twice)
    lem('P12', '12>0 , ~1~2>3', 'CCX21>0 X1 X2 CCX21>3 X1 X2', 'X1 X2 CCX21>3 X1 X2 CCX21>0',
        [('n', 'X1 X2 CCX21>3 X1 X2', 'CCX21>3 CX1>3 CX2>3 X3'),
         ('l', 'CCX21>0 CCX21>3', 'CCX21>3 CCX21>0'),
         ('l', 'CCX21>0 CX1>3', 'CX1>3 CCX21>0'),
         ('l', 'CCX21>0 CX2>3', 'CX2>3 CCX21>0'),
         ('r', 'CCX21>3 CX1>3 CX2>3 X3 CCX21>0'),
         ('n', 'CCX21>3 CX1>3 CX2>3 X3', 'X1 X2 CCX21>3 X1 X2')])
    return out


# ---------------------------------------------------------------- own checker

def own_check(lhs, rhs, steps):
    """lhs, rhs, steps in JSON form (letters ['X', t], ['CX', c, t],
    ['CCX', a, b, t]).  Returns (narrow, rule7) counts."""
    def wires(l):
        return set(l[1:])

    def act(l, x):
        if l[0] == 'X':
            return x ^ (1 << l[1])
        if l[0] == 'CX':
            return x ^ ((x >> l[1] & 1) << l[2])
        return x ^ ((x >> l[1] & x >> l[2] & 1) << l[3])

    def fn(w):
        out = []
        for x in range(16):
            for l in w:
                x = act(l, x)
            out.append(x)
        return out

    def same(u, v):
        return len(u) == len(v) and all(
            [l for l in u if k in wires(l)] == [l for l in v if k in wires(l)] for k in range(4))

    def norm(l):
        return [l[0]] + (sorted(l[1:3], reverse=True) + [l[3]] if l[0] == 'CCX' else l[1:])

    cur = [norm(l) for l in lhs]
    f0 = fn(cur)
    nn = n7 = 0
    for st in steps:
        lin = [norm(l) for l in st['lin']]
        assert same(lin, cur)
        i = st['i']
        if st['kind'] == 'narrow':
            j = st['j']
            new = [norm(l) for l in st['new']]
            tr = set(st['triple'])
            assert len(tr) == 3 and all(wires(l) <= tr for l in lin[i:j] + new)
            assert fn(lin[i:j]) == fn(new)
            cur = lin[:i] + new + lin[j:]
            nn += 1
        else:
            assert st['kind'] == 'rule7'
            # P c P <-> Q c: P = CCX(a, b -> u), c = CX(u -> t), Q = CCX(a, b -> t)
            if st['dir'] == 'fwd':
                P, c, P2 = lin[i:i + 3]
                assert P == P2 and P[0] == 'CCX' and c[0] == 'CX' and c[1] == P[3]
                assert len({P[1], P[2], P[3], c[2]}) == 4
                cur = lin[:i] + [norm(['CCX', P[1], P[2], c[2]]), c] + lin[i + 3:]
            else:
                Q, c = lin[i:i + 2]
                assert Q[0] == 'CCX' and c[0] == 'CX' and c[2] == Q[3]
                assert len({Q[1], Q[2], Q[3], c[1]}) == 4
                P = norm(['CCX', Q[1], Q[2], c[1]])
                cur = lin[:i] + [P, c, P] + lin[i + 2:]
            n7 += 1
        assert fn(cur) == f0
    assert same(cur, [norm(l) for l in rhs])
    return nn, n7


if __name__ == '__main__':
    lib = load_library()
    res = []
    for name, (pair, lhs, rhs, b, used) in build(lib).items():
        js = [pg.step_json(s) for s in b.steps]
        ok, msg = pg.check_derivation(lhs, rhs, js)
        assert ok, (name, msg)
        nn, n7 = own_check(pg.jw(lhs), pg.jw(rhs), js)
        assert nn + n7 == len(js)
        print('%s  %-14s %-34s = %-28s %3d steps = %3d narrow + %2d rule7   (uses %s)' % (
            name, pair, show(lhs), show(rhs), len(js), nn, n7, ','.join(used)), flush=True)
        res.append({'name': name, 'pair': pair, 'lhs': pg.jw(lhs), 'rhs': pg.jw(rhs),
                    'lhs_text': show(lhs), 'rhs_text': show(rhs), 'uses': used,
                    'length': len(js), 'narrow_steps': nn, 'rule7_steps': n7,
                    'checked': 'pg_search.check_derivation and own_check', 'steps': js})
    json.dump(res, open('pairlemmas_raw.json', 'w'))
    print('wrote pairlemmas_raw.json')
