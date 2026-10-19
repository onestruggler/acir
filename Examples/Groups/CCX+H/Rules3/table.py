"""Tables 1 and 2 of Li-Ross-Selinger on eight levels, as in the Agda
constructors (CCX+HH-TwoLevel/Syntactics, Scaled/Syntactics).

A constructor: (name, variables, explicit arguments, lhs, rhs, table)
  explicit arguments: ('lt', x, y) irrelevant x < y; ('ne', x, y) relevant x ≢ y;
                      ('eqk', x, k) toℕ x ≡ k; ('suc', y, x) toℕ y ≡ suc (toℕ x);
                      ('mod', x, r) toℕ x % 2 ≡ r
  sides: lists of ('M', x) ('X', x, y) ('K', a, b, c, d) ('H',)
"""
import itertools

def L(*a): return ('lt',) + a
def N(*a): return ('ne',) + a

T1 = [
 ('r1a', 'a b', [L('a', 'b')], [('X', 'a', 'b'), ('X', 'a', 'b')], []),
 ('r1b', 'a', [], [('M', 'a'), ('M', 'a')], []),
 ('r1c', 'a b c d', [L('a', 'b'), L('b', 'c'), L('c', 'd')],
  [('K', 'a', 'b', 'c', 'd'), ('K', 'a', 'b', 'c', 'd')], []),
 ('r2a', 'a b c d', [L('a', 'b'), L('c', 'd'), N('a', 'c'), N('a', 'd'), N('b', 'c'), N('b', 'd')],
  [('X', 'a', 'b'), ('X', 'c', 'd')], [('X', 'c', 'd'), ('X', 'a', 'b')]),
 ('r2b', 'a b c', [L('a', 'b'), N('c', 'a'), N('c', 'b')],
  [('X', 'a', 'b'), ('M', 'c')], [('M', 'c'), ('X', 'a', 'b')]),
 ('r2c', 'a b c d e f', [L('a', 'b'), L('c', 'd'), L('d', 'e'), L('e', 'f'),
  N('a', 'c'), N('a', 'd'), N('a', 'e'), N('a', 'f'), N('b', 'c'), N('b', 'd'), N('b', 'e'), N('b', 'f')],
  [('X', 'a', 'b'), ('K', 'c', 'd', 'e', 'f')], [('K', 'c', 'd', 'e', 'f'), ('X', 'a', 'b')]),
 ('r2d', 'a b', [N('a', 'b')], [('M', 'a'), ('M', 'b')], [('M', 'b'), ('M', 'a')]),
 ('r2e', 'a b c d e', [L('b', 'c'), L('c', 'd'), L('d', 'e'), N('a', 'b'), N('a', 'c'), N('a', 'd'), N('a', 'e')],
  [('M', 'a'), ('K', 'b', 'c', 'd', 'e')], [('K', 'b', 'c', 'd', 'e'), ('M', 'a')]),
 ('r2f', 'a b c d e f g h', [L('a', 'b'), L('b', 'c'), L('c', 'd'), L('e', 'f'), L('f', 'g'), L('g', 'h')]
  + [N(x, y) for x in 'abcd' for y in 'efgh'],
  [('K', 'a', 'b', 'c', 'd'), ('K', 'e', 'f', 'g', 'h')], [('K', 'e', 'f', 'g', 'h'), ('K', 'a', 'b', 'c', 'd')]),
 ('r3a', 'a a′ b', [L('a', 'a′'), L('a′', 'b'), L('a', 'b')],
  [('X', 'a', 'a′'), ('X', 'a', 'b')], [('X', 'a′', 'b'), ('X', 'a', 'a′')]),
 ('r3b', 'a b b′', [L('a', 'b'), L('b', 'b′'), L('a', 'b′')],
  [('X', 'b', 'b′'), ('X', 'a', 'b')], [('X', 'a', 'b′'), ('X', 'b', 'b′')]),
 ('r3c', 'a b', [L('a', 'b')], [('X', 'a', 'b'), ('M', 'b')], [('M', 'a'), ('X', 'a', 'b')]),
 ('r3d', 'a a′ b c d', [L('a', 'a′'), L('a′', 'b'), L('b', 'c'), L('c', 'd'), L('a', 'b')],
  [('X', 'a', 'a′'), ('K', 'a', 'b', 'c', 'd')], [('K', 'a′', 'b', 'c', 'd'), ('X', 'a', 'a′')]),
 ('r3e', 'a b b′ c d', [L('a', 'b'), L('b', 'b′'), L('b′', 'c'), L('c', 'd'), L('b', 'c'), L('a', 'b′')],
  [('X', 'b', 'b′'), ('K', 'a', 'b', 'c', 'd')], [('K', 'a', 'b′', 'c', 'd'), ('X', 'b', 'b′')]),
 ('r3f', 'a b c c′ d', [L('a', 'b'), L('b', 'c'), L('c', 'c′'), L('c′', 'd'), L('c', 'd'), L('b', 'c′')],
  [('X', 'c', 'c′'), ('K', 'a', 'b', 'c', 'd')], [('K', 'a', 'b', 'c′', 'd'), ('X', 'c', 'c′')]),
 ('r3g', 'a b c d d′', [L('a', 'b'), L('b', 'c'), L('c', 'd'), L('d', 'd′'), L('c', 'd′')],
  [('X', 'd', 'd′'), ('K', 'a', 'b', 'c', 'd')], [('K', 'a', 'b', 'c', 'd′'), ('X', 'd', 'd′')]),
 ('r4a', 'a b c d', [L('a', 'b'), L('b', 'c'), L('c', 'd'), L('b', 'd')],
  [('X', 'a', 'b'), ('K', 'a', 'b', 'c', 'd')],
  [('K', 'a', 'b', 'c', 'd'), ('X', 'b', 'd'), ('M', 'b'), ('M', 'd')]),
 ('r4b', 'a b c d', [L('a', 'b'), L('b', 'c'), L('c', 'd')],
  [('X', 'b', 'c'), ('K', 'a', 'b', 'c', 'd')],
  [('M', 'a'), ('K', 'a', 'b', 'c', 'd'), ('M', 'a'), ('K', 'a', 'b', 'c', 'd'), ('M', 'a')]),
 ('r4c', 'a b c d', [L('a', 'b'), L('b', 'c'), L('c', 'd'), L('b', 'd')],
  [('X', 'c', 'd'), ('K', 'a', 'b', 'c', 'd')], [('K', 'a', 'b', 'c', 'd'), ('X', 'b', 'd')]),
 ('r5a', 'a b c d e f', [L('a', 'b'), L('b', 'c'), L('c', 'd'), L('d', 'e'), L('e', 'f'), L('b', 'd'), L('c', 'e')],
  [('K', 'a', 'b', 'c', 'd'), ('K', 'b', 'd', 'e', 'f')], [('K', 'c', 'd', 'e', 'f'), ('K', 'a', 'b', 'c', 'e')]),
 ('r6a', 'a b c d e f g h', [L('a', 'b'), L('b', 'c'), L('c', 'd'), L('d', 'e'), L('e', 'f'), L('f', 'g'),
  L('g', 'h'), L('a', 'e')],
  [('M', 'a'), ('M', 'e'), ('X', 'a', 'e'), ('K', 'e', 'f', 'g', 'h'), ('K', 'a', 'b', 'c', 'd'), ('X', 'd', 'e'),
   ('K', 'a', 'b', 'c', 'd'), ('K', 'e', 'f', 'g', 'h'), ('X', 'a', 'e'), ('M', 'a'), ('M', 'e')],
  [('K', 'e', 'f', 'g', 'h'), ('K', 'a', 'b', 'c', 'd'), ('X', 'd', 'e'), ('K', 'a', 'b', 'c', 'd'),
   ('K', 'e', 'f', 'g', 'h')]),
]

T2 = [
 ('r7a', '', [], [('H',), ('H',)], []),
 ('r7b', 'a b c d', [L('a', 'b'), L('b', 'c'), L('c', 'd'), ('eqk', 'a', 0), ('eqk', 'b', 1), ('eqk', 'c', 2),
  ('eqk', 'd', 3)], [('H',), ('K', 'a', 'b', 'c', 'd'), ('H',)], [('K', 'a', 'b', 'c', 'd')]),
 ('r7c', 'a b', [L('a', 'b'), ('eqk', 'a', 0), ('eqk', 'b', 1)],
  [('H',), ('M', 'a'), ('H',)], [('M', 'a'), ('X', 'a', 'b'), ('M', 'a')]),
 ('r7d₀', 'x y', [L('x', 'y'), ('suc', 'y', 'x'), ('mod', 'x', 0)],
  [('H',), ('X', 'x', 'y'), ('H',)], [('M', 'y')]),
 ('r7d₁', 'w x y z', [L('w', 'x'), L('x', 'y'), L('y', 'z'), ('suc', 'x', 'w'), ('suc', 'y', 'x'),
  ('suc', 'z', 'y'), ('mod', 'x', 1)],
  [('H',), ('X', 'x', 'y'), ('H',)], [('X', 'x', 'y'), ('K', 'w', 'x', 'y', 'z')]),
]


# variable orders for the dispatch trees (fewer clauses)
ORDER = {'r2c': 'c d e f a b', 'r2e': 'b c d e a', 'r7d₁': 'x y w z'}


def order(con):
    return ORDER.get(con[0], con[1]).split()


def holds(arg, v):
    k = arg[0]
    if k == 'lt':
        return v[arg[1]] < v[arg[2]]
    if k == 'ne':
        return v[arg[1]] != v[arg[2]]
    if k == 'eqk':
        return v[arg[1]] == arg[2]
    if k == 'suc':
        return v[arg[1]] == v[arg[2]] + 1
    if k == 'mod':
        return v[arg[1]] % 2 == arg[2]
    raise ValueError(arg)


def instances(con):
    name, vs, args, lhs, rhs = con
    vs = vs.split()
    out = []
    for vals in itertools.product(range(8), repeat=len(vs)):
        v = dict(zip(vs, vals))
        if all(holds(a, v) for a in args):
            out.append(v)
    return out


def gen_of(g, v):
    """an auxiliary generator as decoder.dec expects"""
    if g[0] == 'H':
        return {'gate': 'IH', 'levels': []}
    return {'gate': g[0], 'levels': [v[x] for x in g[1:]]}


if __name__ == "__main__":
    tot = 0
    for con in T1 + T2:
        n = len(instances(con))
        tot += n
        print(con[0], n)
    print('total', tot)
