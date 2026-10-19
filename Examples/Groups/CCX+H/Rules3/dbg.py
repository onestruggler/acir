import syn
from syn import *
print("A mono", len(AMONO), "A cos", len(ACOS))
import random
rng = random.Random(1)
w = tuple(rng.choice(THETA_T) for _ in range(30))
m = M(w)
for name, reps in [("rev", RC), ("fwd", [tuple(reversed(r)) for r in RC])]:
    for side in ("right", "left"):
        hits = 0
        for r in reps:
            ri = T(M(r))
            d = mat_mul(m, ri) if side == "right" else mat_mul(ri, m)
            if mono(d) is not None: hits += 1
        print(name, side, hits)
