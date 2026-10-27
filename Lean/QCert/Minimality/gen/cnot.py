from search import *
import sys, time

def L(g, off=0): return (g, off)
def rep(w, k): return list(w) * k
X0, X1, T0, T1, CX, SW, W0 = L('X'), L('X', 1), L('T'), L('T', 1), L('CX'), L('SW'), L('w')
T2 = L('T', 2)

axioms = {
  'ω8': (0, rep([W0], 8), []),
  'X2': (1, [X0, X0], []),
  'T8': (1, rep([T0], 8), []),
  'TX': (1, [W0] + rep([T0], 7) + [X0], [X0, T0]),
  'XC': (2, [CX, X0], [X1, CX, X1]),
  'B':  (2, [CX, SW, CX, SW], [SW, CX]),
  'ZC': (2, [CX] + rep([T1], 4), rep([T0], 4) + [CX] + rep([T0], 4)),
  'CPh': (2, [CX, T1, CX], [T1]),
}
syms = {
  'invol': (2, [SW, SW], []),
  'nat1 .X': (2, [X1, SW], [SW, X0]),     # σ * shift X = X * σ (operator) ; time: [shift X, σ] = [σ, X]
  'nat1 .T': (2, [T1, SW], [SW, T0]),
  'nat2 .CX': (3, [L('CX', 1), L('SW'), L('SW', 1)], [L('SW'), L('SW', 1), L('CX')]),
  'nat2 .swap': (3, [L('SW', 1), L('SW'), L('SW', 1)], [L('SW'), L('SW', 1), L('SW')]),
}
fr = Frag({'w': 0, 'X': 1, 'T': 1, 'CX': 2, 'SW': 2}, ['w'], axioms, syms, 'pres')

# Amy–Chen–Ross relations (the other formalisation's `Rel`), translated, time order
targets = {
  'R2': (2, [CX, X0, CX], [X0]),
  'R3': (2, [CX, X1, CX], [X1, X0]),
  'R4': (2, [CX, CX], []),
  'R5': (2, [SW], [CX, SW, CX, SW, CX]),
  'R8': (2, rep([CX, T0, CX], 4), rep([T0], 4) + rep([T1], 4)),
  'R11': (1, [X0, T0, X0], [W0] + rep([T0], 7)),
  'nat1X': (2, [X0, SW], [SW, X1]),
  'nat1T': (2, [T0, SW], [SW, T1]),
  'nat2CX': (3, [CX, L('SW', 1), SW], [L('SW', 1), SW, L('CX', 1)]),
  'nat2SW': (3, [SW, L('SW', 1), SW], [L('SW', 1), SW, L('SW', 1)]),
}

if __name__ == '__main__':
    names = sys.argv[1:] or list(targets)
    lemmas = []
    for nm in names:
        k, l, r = targets[nm]
        t = time.time()
        eqs, steps = search(fr, k, op(l), op(r), lemmas=lemmas, maxlen=int(12), maxnodes=3_000_000)
        print(nm, 'steps' if steps is not None else 'FAILED', None if steps is None else len(steps), '%.1fs' % (time.time() - t))
        if steps is not None:
            assert replay(fr, eqs, op(l), steps) == op(r)
            e2, s2 = prune(eqs, steps)
            print('  eqs:', [e[2] for e in e2])
            print('  steps:', s2)
            lemmas.append((nm, (k, l, r)))

XC = [SW, CX, SW]
T7 = rep([T0], 7)
def chain(n, ways, lemmas, maxlen=12):
    allsteps = []; eqs0 = None
    for a, b in zip(ways, ways[1:]):
        eqs, steps = search(fr, n, op(a), op(b), lemmas=lemmas, maxlen=maxlen, maxnodes=3_000_000)
        if steps is None:
            print('   chain step FAILED', a, '->', b); return None, None
        eqs0 = eqs; allsteps += steps
    assert replay(fr, eqs0, op(ways[0]), allsteps) == op(ways[-1])
    return eqs0, allsteps
