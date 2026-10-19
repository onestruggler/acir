"""The top level of the three-wire tower: the natural rules on three
wires over W(D8), seeded with ThreeQubit's 135 representatives, labels
kept canonical in the nine letters (pipe.py's W(D8) normal form).

Relators: the natural rules at every placement, the involutions, the
commutations of gates on disjoint wires, and every relation of the
two-wire groups on the wires 0, 1 and 1, 2 (completeness on two wires).

    python3 -B top.py        # build, replay, report sizes
"""
import sys, json, time
sys.path.insert(0, '..')
import core as C
import natproof as NP
import proofs as P
import labelled as LB
import pipe as Pp
import partial as PT

gs = PT.gs
GL = gs.index
TQ = json.load(open('/mnt/d/dwork3/acir/Examples/Groups/CCX+HH/ThreeQubit/finite_cosets.json'))
REN = {'X0': 'X0', 'X1': 'X1', 'X2': 'X2', 'CX10': 'CX0', 'CX21': 'CX1',
       'CCX210': 'CCX0', 'HH01': 'HH0', 'HH12': 'HH1'}

def tq_reps():
    # stored lists apply left to right; the matrix order is reversed
    return [tuple(GL[REN[t]] for t in reversed(w)) for w in TQ['representative_words']]

def two_relators():
    rels = []
    for table in (PT.CANLOW, PT.CANHIGH):
        out = set()
        letters = sorted(set(x for w in table.values() for x in w))
        for p, w in table.items():
            for x in letters:
                r = w + (x,)
                rel = r + tuple(reversed(table[PT.ev(r)]))
                if rel:
                    out.add(rel)
        rels.append(sorted(out))
    return rels

def build():
    rels, free, levels = Pp.build()
    d8 = levels[-1]
    macros = {x: Pp.Lv.gates(Pp.Lv.MACRO[x]) for x in Pp.LET}
    ax = NP.axioms(gs)
    two01, two12 = two_relators()
    ax += [P.Axiom(('two01', k), r, ()) for k, r in enumerate(two01)]
    ax += [P.Axiom(('two12', k), r, ()) for k, r in enumerate(two12)]

    class TopTC(LB.LabelledTC):
        def join(tc, left, right):
            lab = tuple(left) + tuple(right)
            nf = d8.canon(Pp.sp(lab))
            if nf == lab:
                return lab, []
            f = tc._add(tc.dec(lab), tc.dec(nf), [(0, ("norm", (lab, nf)), True)])
            return nf, [(0, ("fact", f), True)]

    reps = tq_reps()
    t0 = time.time()
    tc = TopTC(len(gs.names), ax, macros, limit=500_000)
    live = tc.run()
    print('top:', len(live), 'live, defined', len(tc.rep), 'facts', len(tc.facts),
          round(time.time() - t0, 1), 's', flush=True)
    assert len(live) == 135
    table = {}
    for c in live:
        for y in range(len(gs.names)):
            table[(c, y)] = tc.final(c, y)
    return rels, levels, tc, live, table, reps

if __name__ == '__main__':
    rels, levels, tc, live, table, reps = build()
    roots = [f for (_, _, f) in table.values()]
    cl = Pp.closure(tc, roots)
    norms = sum(1 for f in cl if tc.facts[f].steps and tc.facts[f].steps[0][1][0] == 'norm')
    used = {}
    for f in cl:
        for (_, (kind, k), _) in tc.facts[f].steps:
            if kind == 'ax':
                nm = tc.axioms[k].name
                used[nm[0]] = used.get(nm[0], 0) + 1
    print('closure', len(cl), 'facts,', norms, 'norm; steps', sum(len(tc.facts[f].steps) for f in cl))
    print('axiom kinds used:', used)
