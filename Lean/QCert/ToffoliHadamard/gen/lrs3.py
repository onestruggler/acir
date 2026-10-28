from lrs import *
import sys
N = lambda a: ('n', a); X = lambda a, b: ('x', a, b); K = lambda *q: ('k',) + q
pair_rule = {}
for k, (l, r, nm) in enumerate(RS.rules):
    if len(r) == 0 and len(l) == 2 and l[0] == l[1]:
        pair_rule[l[0]] = k
class RS2:
    def __init__(self, base, S):
        self.b = base; self.S = S
        self.rules = base.rules
    def neighbours(self, w, maxlen):
        yield from self.b.neighbours(w, maxlen)
        if len(w) + 2 <= maxlen:
            for g in self.S:
                for i in range(len(w) + 1):
                    yield w[:i] + bytes([g, g]) + w[i:], (i, pair_rule[g], False)
def search(a, b, S, ex, limit):
    rs = RS2(RS, [GI[g] for g in S])
    return bidir(rs, enc(a), enc(b), maxlen=max(len(a), len(b)) + ex, limit=limit)
tests = {
  "CZ01": ([K(0,1,2,3), K(4,5,6,7), X(5,7), X(4,6), K(0,1,2,3), K(4,5,6,7)], [N(6), N(7)]),
  "Z1": ([K(0,1,2,3), K(4,5,6,7), X(5,7), X(4,6), X(1,3), X(0,2), K(0,1,2,3), K(4,5,6,7)], [N(2), N(3), N(6), N(7)]),
  "K01": ([X(3,6), X(1,4), K(0,1,2,3), K(4,5,6,7), X(3,6), X(1,4)], [K(0,2,4,6), K(1,3,5,7)]),
}
if __name__ == "__main__":
  for nm, (a, b) in tests.items():
      S = sorted(set(a) | set(b))
      for ex in (2, 4):
          t = time.time()
          r = search(a, b, S, ex, 3_000_000)
          print(nm, ex, None if r is None else len(r), round(time.time() - t, 1), flush=True)
          if r: break
