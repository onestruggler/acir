import itertools, random
from table import T1
from disp_count import count
con = [c for c in T1 if c[0] == 'r2f'][0]
orders = ['a b c d e f g h', 'a e b f c g d h', 'a e f g h b c d', 'e f g h a b c d', 'a h b g c f d e', 'h d g c f b e a']
for o in orders:
    print(o, count(con, o.split()))
rng = random.Random(1)
best = None
for _ in range(300):
    o = list('abcdefgh'); rng.shuffle(o)
    c = count(con, o)
    if best is None or c < best[0]:
        best = (c, ' '.join(o))
print('best random', best)
