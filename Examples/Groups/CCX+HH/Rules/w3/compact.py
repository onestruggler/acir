"""Short decoders for ThreeQubit's compact base letters (x_i exchanges
levels i, i+1; p_i negates levels 0 and i+1) and the 105 decoded base
relations, as words in the tower letters.

Level l = x0 + 2 x1 + 4 x2 (wire 0 the least significant bit).
x_i = pi CCX0 pi^-1 and p_i = pi CZ pi^-1, with CZ = HH0 CX1 HH0 (which
negates the levels 6, 7) and pi a shortest classical word sending the
levels 6, 7 to the right pair.

    python3 -B compact.py          # print decoders and relation lengths
"""
import sys, itertools
from collections import deque
sys.path.insert(0, '..')
import levels as Lv

Lv.MACRO['CZ'] = 'HH0 CX1 HH0'
Lv.WIRES['CZ'] = {1, 2}
Lv.SPELL['CZ'] = {0, 1, 2}
Lv.PERM['CZ'] = Lv.rep.evaluate(Lv.gates(Lv.MACRO['CZ']))

CL = ['X0', 'X1', 'X2', 'CX0', 'CX1', 'CXr0', 'CXr1', 'CCX0']

def level_perm(word):
    """The permutation of the eight levels of a classical word (the word
    acts as the matrix product, the last letter first)."""
    def act(x, l):
        b = [(l >> k) & 1 for k in range(3)]
        if x == 'X0': b[0] ^= 1
        elif x == 'X1': b[1] ^= 1
        elif x == 'X2': b[2] ^= 1
        elif x == 'CX0': b[0] ^= b[1]
        elif x == 'CX1': b[1] ^= b[2]
        elif x == 'CXr0': b[1] ^= b[0]
        elif x == 'CXr1': b[2] ^= b[1]
        elif x == 'CCX0': b[0] ^= b[1] & b[2]
        return b[0] + 2 * b[1] + 4 * b[2]
    out = []
    for l in range(8):
        m = l
        for x in reversed(word):
            m = act(x, m)
        out.append(m)
    return tuple(out)

def bfs():
    best = {tuple(range(8)): ()}
    q = deque([()])
    while q:
        w = q.popleft()
        for x in CL:
            w2 = w + (x,)
            p = level_perm(w2)
            if p not in best:
                best[p] = w2
                q.append(w2)
    return best

def gate_len(word):
    return sum(len(Lv.MACRO[x].split()) for x in word)

BEST = bfs()

def conj_word(pair):
    """Shortest pi (in gates) with {pi(6), pi(7)} = pair."""
    cands = [w for p, w in BEST.items() if {p[6], p[7]} == set(pair)]
    return min(cands, key=lambda w: (gate_len(w), w))

DEC = {}
for i in range(7):
    w = conj_word((i, i + 1))
    DEC[f'x{i}'] = w + ('CCX0',) + tuple(reversed(w))
    w = conj_word((0, i + 1))
    DEC[f'p{i}'] = w + ('CZ',) + tuple(reversed(w))

def relations():
    out = []
    for i in range(7):
        out.append((f'phase-square-{i}', [f'p{i}'] * 2, []))
    for i, j in itertools.combinations(range(7), 2):
        out.append((f'phase-commute-{i}-{j}', [f'p{i}', f'p{j}'], [f'p{j}', f'p{i}']))
    for i in range(7):
        out.append((f'exchange-square-{i}', [f'x{i}'] * 2, []))
    for i in range(6):
        out.append((f'braid-{i}', [f'x{i}', f'x{i+1}', f'x{i}'], [f'x{i+1}', f'x{i}', f'x{i+1}']))
    for i, j in itertools.combinations(range(7), 2):
        if j > i + 1:
            out.append((f'exchange-commute-{i}-{j}', [f'x{i}', f'x{j}'], [f'x{j}', f'x{i}']))
    for i in range(7):
        for j in range(7):
            if i == 0:
                action = ['p0'] if j == 0 else ['p0', f'p{j}']
            elif j == i - 1:
                action = [f'p{i}']
            elif j == i:
                action = [f'p{i-1}']
            else:
                action = [f'p{j}']
            out.append((f'cross-{i}-{j}', [f'x{i}', f'p{j}'], action + [f'x{i}']))
    assert len(out) == 105
    return out

def decode(letters):
    return tuple(t for l in letters for t in DEC[l])

def relator(l, r):
    return decode(l) + tuple(reversed(decode(r)))

if __name__ == '__main__':
    for k, v in DEC.items():
        print(k, ' '.join(v), ' gates', gate_len(v))
    lens = []
    for name, l, r in relations():
        w = relator(l, r)
        assert Lv.ev(w) == Lv.rep.identity, name
        lens.append(gate_len(w))
    print('relation gate lengths: max', max(lens), 'mean', round(sum(lens) / len(lens), 1))
