"""The derivations of the layer below four wires, by Knuth-Bendix completion.

    python capped.py 1500 600 narrow.py 2      (two wires)
    python capped.py 1500 600 narrow.py 3      (three wires)

On k wires the circuits over X, CX, CCX and Ex are the permutations of the
2^k states, which Examples.Groups.Symmetric presents by the transpositions
of two consecutive points.  Numbering the states along the Gray code, the
transposition of the positions d, d + 1 is an edge Toffoli Theta_d: NOT on
the wire that changes, controlled by the other wires, between NOT gates on
the controls that are 0 and the swaps that bring the wires into place.

The Reidemeister-Schreier step from that presentation needs, as
consequences of the rules (1)-(6): the Coxeter relations between the
Theta_d (order, braid, far), and each gate as the word in the Theta_d of
its permutation.  This script finds a derivation of each by proof-producing
Knuth-Bendix completion (Examples/Independence/gen/kb.py) of the rules at
that width, and writes them, with the rules they depend on, as JSON.

Letters, one character each (wire 0 is the bottom wire):
    a b d   X on wires 0, 1, 2
    c e     CX with control 1, target 0; with control 2, target 1
    s t     Ex on wires 0 1; on wires 1 2
    T       CCX with controls 1 2, target 0
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', '..', 'Independence', 'gen'))
from kb import KB  # noqa: E402

sys.dont_write_bytecode = True

# ----------------------------------------------------------------------
# Semantics: a state is an integer, bit k the bit of wire k.


def bit(s, k):
    return (s >> k) & 1


def fx(k):
    return lambda s: s ^ (1 << k)


def fcx(k):
    return lambda s: s ^ (bit(s, k + 1) << k)


def fex(k):
    def f(s):
        u, v = bit(s, k), bit(s, k + 1)
        return s & ~(3 << k) | (v << k) | (u << (k + 1))
    return f


def fccx(k):
    return lambda s: s ^ ((bit(s, k + 1) & bit(s, k + 2)) << k)


GATE = {'a': fx(0), 'b': fx(1), 'd': fx(2), 'c': fcx(0), 'e': fcx(1),
        's': fex(0), 't': fex(1), 'T': fccx(0)}
NAME = {'a': 'X0', 'b': 'X1', 'd': 'X2', 'c': 'CX0', 'e': 'CX1',
        's': 'Ex0', 't': 'Ex1', 'T': 'CCX0'}


def perm(word, k):
    """The function of a word on the states of k wires, as a tuple."""
    out = []
    for s in range(1 << k):
        for g in word:
            s = GATE[g](s)
        out.append(s)
    return tuple(out)


def gray(i):
    return i ^ (i >> 1)


# ----------------------------------------------------------------------
# The rules at each width: (name, lhs, rhs), every one an instance of a
# rule of Theory.agda, of a law of the swap or of a structural rule, on
# the wires where it is an axiom or its padding to the bottom wires.

RULES = {
    2: [
        ('r1', 'aa', ''), ('r1^', 'bb', ''), ('comm-ab', 'ba', 'ab'),
        ('r2', 'cbcb', 'a'), ('r3', 'cscsc', 's'),
        ('ss', 'ss', ''), ('nat-a', 'as', 'sb'),
    ],
    3: [
        ('r1', 'aa', ''), ('r1^', 'bb', ''), ('r1^^', 'dd', ''),
        ('comm-ab', 'ba', 'ab'), ('comm-ad', 'da', 'ad'),
        ('comm-bd', 'db', 'bd'),
        ('comm-dc', 'dc', 'cd'), ('comm-ds', 'ds', 'sd'),
        ('comm-ea', 'ea', 'ae'), ('comm-ta', 'ta', 'at'),
        ('r2', 'cbcb', 'a'), ('r2^', 'eded', 'b'),
        ('r3', 'cscsc', 's'), ('r3^', 'etete', 't'),
        ('ss', 'ss', ''), ('tt', 'tt', ''),
        ('nat-a', 'as', 'sb'), ('nat-b', 'bt', 'td'),
        ('r4', 'TdTd', 'c'), ('r5', 'tTt', 'T'),
        ('r6', 'scsTscs', 'sTsTsTs'),
        ('nat-c', 'cts', 'tse'), ('yb', 'sts', 'tst'),
    ],
}

ORDER = {2: 'abcs', 3: 'abdcestT'}

# The edge Toffolis along the Gray code.
THETA = {
    2: ['bcb', 'scs', 'c'],
    3: ['bdTdb', 'dsTsd', 'dTd', 'atsTsta', 'T', 'sTs', 'bTb'],
}

# The gates on their own wires as words in the transpositions.
GATES = {
    2: {'a': [0, 2], 'c': [2], 's': [1, 2, 1]},
    3: {'a': [0, 2, 4, 6], 'c': [2, 4], 'T': [4],
        's': [1, 2, 1, 4, 5, 4],
        't': [2, 3, 4, 5, 4, 3, 2, 3, 4, 5, 6, 5, 4, 3]},
}


def targets(k):
    th = THETA[k]
    n = len(th)
    out = []
    for d in range(n):
        out.append(('order%d' % d, th[d] + th[d], ''))
    for d in range(n - 1):
        out.append(('braid%d' % d, th[d] + th[d + 1] + th[d],
                    th[d + 1] + th[d] + th[d + 1]))
    for d in range(n):
        for e in range(d + 2, n):
            out.append(('far%d_%d' % (d, e), th[e] + th[d], th[d] + th[e]))
    for g, w in GATES[k].items():
        out.append(('gate-' + NAME[g], g, ''.join(th[i] for i in w)))
    return out


def check_data(k):
    size = 1 << k
    pos = {gray(i): i for i in range(size)}
    for name, l, r in RULES[k]:
        assert perm(l, k) == perm(r, k), name
    for d, w in enumerate(THETA[k]):
        p = perm(w, k)
        want = list(range(size))
        want[gray(d)], want[gray(d + 1)] = gray(d + 1), gray(d)
        assert p == tuple(want), ('theta', d)
    for g, w in GATES[k].items():
        # the word in transpositions, in diagram order, on positions
        q = list(range(size))
        for i in w:
            q = [i + 1 if x == i else i if x == i + 1 else x for x in q]
        p = perm(g, k)
        assert all(pos[p[gray(i)]] == q[i] for i in range(size)), g
    for name, l, r in targets(k):
        assert perm(l, k) == perm(r, k), name


def main():
    k = int(sys.argv[1])
    maxrules = int(sys.argv[2]) if len(sys.argv) > 2 else 20000
    check_data(k)
    tg = targets(k)
    kb = KB(ORDER[k], RULES[k], maxrules=maxrules)

    def done():
        return all(kb.prove(l, r) is not None for _, l, r in tg)
    try:
        kb.complete(until=done, every=50)
    except RuntimeError as err:
        print('stopped:', err)
    proved = {}
    for name, l, r in tg:
        ch = kb.prove(l, r)
        if ch is not None:
            proved[name] = ch
    print('rules: %d (%d live); targets proved: %d of %d' % (
        len(kb.rules), sum(1 for x in kb.rules if x[3]), len(proved),
        len(tg)))
    missing = [name for name, _, _ in tg if name not in proved]
    if missing:
        print('not proved:', ' '.join(missing))
    need = kb.needed(list(proved.values()))
    print('rules the proofs depend on: %d; proof steps: %d' % (
        len(need), sum(len(ch) - 1 for ch in proved.values())))
    rules = []
    for i in need:
        l, r, pf, _ = kb.rules[i]
        ch = kb.rule_chain(i)
        rules.append({'id': i, 'lhs': l, 'rhs': r,
                      'axiom': None if ch is not None else [pf[1], pf[2]],
                      'chain': ch})
    longest = max([len(x['chain']) - 1 for x in rules if x['chain']] + [0])
    print('derived rules: %d, longest chain %d, steps in all %d' % (
        sum(1 for x in rules if x['chain']), longest,
        sum(len(x['chain']) - 1 for x in rules if x['chain'])))
    out = {'width': k, 'order': ORDER[k], 'names': NAME,
           'axioms': RULES[k], 'theta': THETA[k], 'gates': GATES[k],
           'rules': rules,
           'targets': [{'name': n, 'lhs': l, 'rhs': r,
                        'chain': proved.get(n)} for n, l, r in tg]}
    with open(os.path.join(HERE, 'narrow%d.json' % k), 'w') as fh:
        json.dump(out, fh)
    print('wrote narrow%d.json' % k)


if __name__ == '__main__':
    main()
