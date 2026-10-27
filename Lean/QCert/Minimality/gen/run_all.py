from cnot import *
import json, time
lemmas = []
results = {}
def doit(name, n, l, r, maxlen=12, ways=None):
    t = time.time()
    if ways is None:
        eqs, steps = search(fr, n, op(l), op(r), lemmas=lemmas, maxlen=maxlen, maxnodes=3_000_000)
    else:
        eqs, steps = chain(n, ways, lemmas, maxlen=maxlen)
    print(name, None if steps is None else len(steps), '%.1fs' % (time.time() - t), flush=True)
    if steps is None: return
    e2, s2 = prune(eqs, steps)
    assert replay(fr, e2, op(l), s2) == op(r)
    results[name] = (n, l, r, [e[2] for e in e2], s2)
    lemmas.append((name, (n, l, r)))

doit('CPhr', 2, XC + [T0] + XC, [T0])
ways = [[CX, CX], [CX, CX, T0] + T7, [CX, CX] + XC + [T0] + XC + T7, [CX, SW, CX, T0] + XC + T7,
        [SW, CX, SW, T0] + XC + T7, XC + [T0] + XC + T7, [T0] + T7, []]
doit('R4', 2, [CX, CX], [], maxlen=16, ways=ways)
for nm in ['R11', 'R2', 'R3', 'R5', 'nat1X', 'nat1T', 'R8', 'nat2CX', 'nat2SW']:
    k, l, r = targets[nm]
    doit(nm, k, l, r, maxlen=14)
json.dump(results, open('cnot_derivs.json', 'w'))
