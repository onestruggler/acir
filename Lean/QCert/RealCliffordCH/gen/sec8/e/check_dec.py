"""The decoding preserves the semantics (in the Gray basis) on every proper letter, n = 3, 4."""
import itertools, random
from decode import *
r = random.Random(3)
for n in (3, 4):
    N = 2 ** n; bad = 0; tot = 0
    letters = []
    for a in range(N):
        for c in range(N): letters.append(Zz(a, c))
    for a, c, d in itertools.product(range(N), repeat=3):
        if c != d: letters.append(Zx(a, c, d))
    for _ in range(150):
        a, b, c, d = [r.randrange(N) for _ in range(4)]
        if a != b and c != d: letters.append(Xx(a, b, c, d)); letters.append(Hh(a, b, c, d))
    for p in letters:
        tot += 1
        if not np.allclose(csemP(n, dec(n, p)), psem(N, p)):
            bad += 1
            if bad < 5: print('bad', n, p)
    print(n, tot, 'bad', bad)
