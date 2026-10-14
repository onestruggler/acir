# The shortest equations between P' words that carry relation (16):
# true in U_N(Z[1/2,i]) but false in the model K' = -K of every other
# two-level relation (tM16.py).  Any complete rule set for P' needs
# one; these are the candidates.  Words over the letters of csP.letters
# (iib, mX, XX, KKb), equations w1 = w2 with |w1| + |w2| <= L.
import sys
from itertools import product
import csP
import tM16

N = int(sys.argv[1]) if len(sys.argv) > 1 else 5
L = int(sys.argv[2]) if len(sys.argv) > 2 else 4
tM16.N = N

Km = tM16.Kmodel(-1)
model = tM16.letter_model(Km)
true = csP.letters(N)
KINDS = set(sys.argv[3].split(',')) if len(sys.argv) > 3 else {'iib','mX','XX','KKb'}
names = sorted(x for x in true if x[0] in KINDS)
mm = csP.matmul
key = csP.key

def words(maxlen):
    # all words up to maxlen: (word, true matrix, model matrix)
    out = [((), csP.ident(N), csP.ident(N))]
    frontier = out[:]
    for _ in range(maxlen):
        nxt = []
        for w, T, M in frontier:
            for x in names:
                nxt.append((w + (x,), mm(T, true[x]), mm(M, model(x))))
        out += nxt
        frontier = nxt
    return out

half = (L + 1) // 2
ws = words(half)
print(f'N={N}: {len(names)} letters, {len(ws)} words up to length {half}', flush=True)
byT = {}
for w, T, M in ws:
    byT.setdefault(key(T), []).append((w, key(M)))
found = []
for k, group in byT.items():
    if len(group) < 2: continue
    mk = {}
    for w, m in group:
        mk.setdefault(m, []).append(w)
    if len(mk) > 1:
        reps = sorted((min(v, key=len) for v in mk.values()), key=len)
        a, b = reps[0], reps[1]
        if len(a) + len(b) <= L:
            found.append((len(a) + len(b), a, b))
found.sort()
print(f'{len(found)} candidate equations; the shortest:')
for n, a, b in found[:15]:
    print(n, ' . '.join(map(str, a)) or 'eps', ' = ', ' . '.join(map(str, b)) or 'eps')
