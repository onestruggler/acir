"""Three wires: a tower W(E8) > W(D8) > S8 > K > Z2^3 > 1 for the
natural rules, measured by plain coset enumeration (no proofs).

W(D8), the even signed permutations of the eight levels, is the
stabilizer of the coordinate frame (index 135); S8 the classical
permutations (index 128 in W(D8)); K = <X i, CX i, CCX0> (order 128,
index 315 in S8); Z2^3 = <X0, X1, X2> (index 16 in K).

For each level the relators are the natural rules at every placement
(top level), and the script reports the index and the number of cosets
the enumeration defined, which bounds the size of a proof-producing
version.

    python3 -B d8tower.py
"""
import sys, time
sys.path.insert(0, '..')
import core as C
import natproof as NP

gs = C.GateSet(3)
rep = C.PermRep(gs)
L = gs.index

def w(text):
    out = []
    for t in text.split():
        if t.startswith('CXr'):
            i = int(t[3:]); out += [L[f'HH{i}'], L[f'CX{i}'], L[f'HH{i}']]
        elif t.startswith('Z'):
            i = int(t[1:])
            # Z on wire i: HH on wires (i-1, i) or (i, i+1) around X i
            j = i - 1 if i > 0 else i
            out += [L[f'HH{j}'], L[f'X{i}'], L[f'HH{j}']]
        else:
            out.append(L[t])
    return tuple(out)

def order(words):
    seen = {rep.identity}; frontier = [rep.identity]
    gens = [rep.evaluate(x) for x in words]
    while frontier:
        new = []
        for p in frontier:
            for g in gens:
                q = tuple(g[x] for x in p)
                if q not in seen:
                    seen.add(q); new.append(q)
        frontier = new
    return len(seen)

relators = [tuple(a.lhs) + tuple(reversed(a.rhs)) for a in NP.axioms(gs)]

LEVELS = {
    'Z2^3': ['X0', 'X1', 'X2'],
    'K': ['X0', 'X1', 'X2', 'CX0', 'CX1', 'CCX0'],
    'S8': ['X0', 'X1', 'X2', 'CX0', 'CX1', 'CCX0', 'CXr0', 'CXr1'],
    'WD8': ['X0', 'X1', 'X2', 'CX0', 'CX1', 'CCX0', 'CXr0', 'CXr1', 'Z1'],
}

if __name__ == '__main__':
    for name in (sys.argv[1:] or ['WD8']):
        gens = LEVELS[name]
        words = [w(g) for g in gens]
        o = order(words) if name != 'WD8' else None
        t0 = time.time()
        e = C.Enumeration(len(gs.names), relators, words, limit=3_000_000)
        try:
            idx = e.run()
        except OverflowError:
            idx = None
        print(name, 'order', o, 'index', idx, 'defined', len(e.table),
              'time', round(time.time() - t0, 1), flush=True)
