"""Three wires, NaturalP letters (the swap a gate): which subgroups are
presented by their own rules once the relations of the affine group and
of the two-wire groups are taken as given (affine completeness and
completeness on two wires, both proved)?

Letters: X0 X1 X2 CX0 CX1 SW0 SW1 CCX0 HH0 HH1, as permutations of the
E8 orbit.  "Free" relators: the Schreier relators of a finite subgroup
in its letters (every c·y = d of its BFS table gives rep c y rep d⁻¹).

    python3 -B classfree.py
"""
import sys
from collections import deque
sys.path.insert(0, '..')
import core as C

gs = C.GateSet(3)
rep = C.PermRep(gs)
L = gs.index
E = {}
for n in ['X0', 'X1', 'X2', 'CX0', 'CX1', 'CCX0', 'HH0', 'HH1']:
    E[n] = (L[n],)
E['SW0'] = tuple(L[t] for t in 'CX0 HH0 CX0 HH0 CX0'.split())
E['SW1'] = tuple(L[t] for t in 'CX1 HH1 CX1 HH1 CX1'.split())
NAMES = ['X0', 'X1', 'X2', 'CX0', 'CX1', 'SW0', 'SW1', 'CCX0', 'HH0', 'HH1']
IX = {n: k for k, n in enumerate(NAMES)}
PERM = {n: rep.evaluate(E[n]) for n in NAMES}

def mul(p, q):
    """The element of word p ++ q."""
    return tuple(p[i] for i in q)

def bfs(letters):
    best = {rep.identity: ()}
    q = deque([rep.identity])
    while q:
        p = q.popleft()
        for x in letters:
            r = mul(p, PERM[x])
            if r not in best:
                best[r] = best[p] + (x,)
                q.append(r)
    return best

def inverse_word(w):
    return tuple(reversed(w))       # every letter is an involution

def schreier(letters):
    table = bfs(letters)
    rels = set()
    for p, w in table.items():
        for x in letters:
            r = mul(p, PERM[x])
            rel = w + (x,) + inverse_word(table[r])
            if rel:
                rels.add(tuple(IX[t] for t in rel))
    return table, sorted(rels, key=len)

def free_relators(groups):
    out = set()
    for letters in groups:
        _, rels = schreier(letters)
        out |= set(rels)
    for n in NAMES:
        out.add((IX[n], IX[n]))
    return sorted(out, key=len)

AFF = ['X0', 'X1', 'X2', 'CX0', 'CX1', 'SW0', 'SW1']
P01 = ['X0', 'X1', 'CX0', 'SW0', 'HH0']
P12 = ['X1', 'X2', 'CX1', 'SW1', 'HH1']

def w(text):
    return tuple(IX[t] for t in text.split())

RULES = {
    'CCX-sym': ('SW1 CCX0 SW1', 'CCX0'),
    'CCX-neg': ('X1 CCX0 X1', 'CCX0 SW1 CX0 SW1'),
    'CCX-XC': ('CCX0 SW0 CX0 SW0 CCX0 SW0 CX0 SW0', 'SW0 CCX0 SW0 CCX0'),
    'CCX-HH': ('CCX0 SW0 CX0 SW0 HH0 SW0 CX0 SW0', 'SW0 CX0 SW0 HH0 SW0 CX0 SW0 CCX0'),
    'HH-swap0': ('SW0 HH1 SW0', 'HH0 HH1'),
    'HH-swap1': ('SW1 HH0 SW1', 'HH0 HH1'),
    'HH-nat': ('HH0 SW1 SW0', 'SW1 SW0 HH1'),
}

def rel(name):
    l, r = RULES[name]
    return w(l) + tuple(reversed(w(r)))

def check(title, letters, free_groups, rules, sub, expected, limit=3_000_000):
    rels = [r for r in free_relators(free_groups) if all(NAMES[x] in letters for x in r)]
    rels += [rel(n) for n in rules]
    # renumber letters
    loc = {IX[n]: k for k, n in enumerate(letters)}
    rels = [tuple(loc[x] for x in r) for r in rels]
    subw = [tuple(loc[IX[t]] for t in s.split()) for s in sub]
    got = C.index(len(letters), rels, subw, limit=limit)
    print(f'{title}: index {got} (expected {expected}), relators {len(rels)}', flush=True)

if __name__ == '__main__':
    a = len(bfs(AFF)); s8 = len(bfs(AFF + ['CCX0']))
    print('|Aff| =', a, '|S8| =', s8)
    check('S8 over Aff, rules CCX-sym CCX-neg CCX-XC',
          AFF + ['CCX0'], [AFF, P01, P12], ['CCX-sym', 'CCX-neg', 'CCX-XC'],
          AFF, s8 // a)
