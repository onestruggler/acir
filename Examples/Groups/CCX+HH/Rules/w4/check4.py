#!/usr/bin/env python3
"""Four wires: do the natural rules present the Clifford and the
classical subgroups?

    python3 -B check4.py clifford|classical

Coset enumeration (../tc) of a subgroup K in the group P_L presented by
the relators that use only the letters L; |P_L| <= [P_L : K] |K|.  The
true orders come from Schreier-Sims on a faithful orbit."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import core as C
import staged as S
from classical3 import CLASSICAL_RULES
from natural3 import TOFFOLI_CNOT, HADAMARD_RULES
import ss

FOUR = ["CCX1 CX0 CCX1 CX0 = SW0 CCX1 SW0",      # Toffoli = [Toffoli, CNOT]
        "SW0 SW1 SW2 CCX0 SW2 SW1 SW0 = CCX1"]   # Toffoli moved up a wire

gs = C.GateSet(4)
DER = {}
for i in range(3):
    DER[f"CXr{i}"] = f"HH{i} CX{i} HH{i}"
for i in range(3):
    DER[f"SW{i}"] = f"CX{i} HH{i} CX{i} HH{i} CX{i}"
a = S.Alphabet(gs, DER)
L = a.index


def rep_on(letters, scale=4):
    """Permutations of the orbit of scale·e_i under the letters."""
    dim = 16
    acts = [a.primitive((g,)) for g in letters]
    def act(word, v):
        for g in reversed(word):
            v = gs.actions[g](v)
        return v
    start = [tuple(scale if j == i else 0 for j in range(dim)) for i in range(dim)]
    idx = {v: k for k, v in enumerate(start)}
    pts = list(start)
    fr = list(start)
    while fr:
        new = []
        for v in fr:
            for w in acts:
                u = act(w, v)
                if u not in idx:
                    idx[u] = len(pts)
                    pts.append(u)
                    new.append(u)
        fr = new
        if len(pts) > 200000:
            raise RuntimeError('orbit too large')
    return [tuple(idx[act(w, v)] for v in pts) for w in acts], len(pts)


def order(letters):
    perms, n = rep_on(letters)
    return ss.order(perms), n


def all_rules():
    texts = CLASSICAL_RULES + [TOFFOLI_CNOT["commutator"]] + HADAMARD_RULES + FOUR
    rels = []
    for t in texts:
        rels += S.rule(a, t)
    return rels


def run(letters, sub):
    letters = [L[n] for n in letters]
    sub = [L[n] for n in sub]
    rels = a.structural(letters) + all_rules() + a.definitions()
    full, n = order(letters)
    k, _ = order(sub)
    print('|group| =', full, ' orbit', n, ' |K| =', k, ' index should be', full // k, flush=True)
    idx = S.restricted_index(a, rels, letters, sub, limit=20_000_000)
    print('enumerated index of K:', idx, flush=True)
    return idx, full // k


if __name__ == '__main__':
    what = sys.argv[1]
    if what == 'clifford':
        lets = [f"X{i}" for i in range(4)] + [f"{g}{i}" for g in ("CX", "CXr", "HH", "SW") for i in range(3)]
        sub = [x for x in lets if all(w < 3 for w in a.wires[L[x]])]
        run(lets, sub)
    elif what == 'classical':
        lets = [f"X{i}" for i in range(4)] + [f"{g}{i}" for g in ("CX", "CXr", "SW") for i in range(3)] + ["CCX0", "CCX1"]
        # the subgroup preserving the partition by wire 3
        sub = ["X0", "X1", "X2", "X3", "CX0", "CX1", "CX2", "CXr0", "CXr1", "SW0", "SW1", "CCX0", "CCX1"]
        run(lets, sub)
