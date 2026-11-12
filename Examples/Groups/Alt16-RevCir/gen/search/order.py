"""The order relation K^3 = id, composed from two lemmas.

    python ..\\capped.py 1500 600 order.py      -> macro_order.json

A direct search does not find it.  With K = (T C)^2, T = 02>1, C = 13>0,
t = CX from wire 0 to wire 1 and z = C t C t C, a word on the wires
0 1 3:

    L1   T C T C T = t C T C t        (macro_L1.json, by search)
    Tz   T z = z T                    (macro_Tz.json, by search)

so K^3 = (T C T C T) C (T C T C T) C = t C T z T C t C = t C z T T C t C,
a word on three wires equal to the identity.  This script writes that out
as one macro derivation and checks it.
"""
import json
import os
import sys

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import macro as M          # noqa: E402


def triple_of(g):
    for tm in M.TRIPLES:
        if not (M.MASK[g] & ~tm):
            return [k for k in range(4) if tm >> k & 1]


def apply_lemma(cur, pos, lem):
    """cur = pre + lhs + post  ->  pre + rhs + post, by the lemma's stored
    reduction of lhs rhs^-1 to the empty word.  Returns (steps, word)."""
    l, r = tuple(lem['lhs']), tuple(lem['rhs'])
    cur = tuple(cur)
    assert cur[pos:pos + len(l)] == l
    pre, post = cur[:pos], cur[pos + len(l):]
    steps = []
    # insert r^-1 r after lhs, one cancelling pair at a time
    mid = ()
    for k in reversed(range(len(r))):
        x = r[k]
        at = len(pre) + len(l) + len(mid) // 2
        lin = pre + l + mid + post
        steps.append({'kind': 'narrow', 'triple': triple_of(x), 'lin': list(lin),
                      'i': at, 'j': at, 'new': [x, x]})
        h = len(mid) // 2
        mid = mid[:h] + (x, x) + mid[h:]
    assert mid == tuple(reversed(r)) + r
    tail = r + post
    for st in lem['steps']:
        s2 = dict(st)
        s2['lin'] = list(pre) + list(st['lin']) + list(tail)
        s2['i'] = st['i'] + len(pre)
        if 'j' in st:
            s2['j'] = st['j'] + len(pre)
        steps.append(s2)
    return steps, pre + r + post


def main():
    L1 = json.load(open(os.path.join(HERE, 'macro_L1.json')))
    Tz = json.load(open(os.path.join(HERE, 'macro_Tz.json')))
    T, C = L1['lhs'][0], L1['lhs'][1]
    start = (T, C) * 6                       # K^3
    steps = []
    cur = start
    for pos, lem in ((0, L1), (6, L1), (2, Tz)):
        st, cur = apply_lemma(cur, pos, lem)
        steps += st
    # what is left is on three wires
    w, nst = M.normalise(M.canon(cur))
    steps += nst
    assert w == (), M.show(w)
    assert M.check(start, (), steps)
    json.dump({'name': 'order', 'found': True, 'checked': True,
               'composed_from': ['L1', 'L1', 'Tz'],
               'lhs': list(start), 'rhs': [], 'relator': list(start),
               'relator_text': M.show(start), 'steps': steps,
               'gates': [M.gname(i) for i in range(M.NG)],
               'narrow_steps': sum(1 for s in steps if s['kind'] == 'narrow'),
               'pair_steps': sum(1 for s in steps if s['kind'] == 'pair'),
               'expand_steps': sum(1 for s in steps if s['kind'] == 'expand')},
              open(os.path.join(HERE, 'macro_order.json'), 'w'))
    print('order: %d steps' % len(steps))


if __name__ == '__main__':
    main()
