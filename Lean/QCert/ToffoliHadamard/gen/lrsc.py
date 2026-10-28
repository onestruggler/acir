"""LRS-level search in C (7-bit letters) with rotations of Table 1 relators."""
from paths import work, data, module
import subprocess, time, sys
from cbfs import Relators
from paths import bfs_cmd
from lrs import GENS, GI, T1
from model import lev

class CSearch7:
    def __init__(self, maxlhs, rels):
        self.rels = rels
        self.p = subprocess.Popen(bfs_cmd("bfs7"), stdin=subprocess.PIPE,
                                  stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True, bufsize=1)
        out = [f"{len(GENS)} {maxlhs} {len(rels.rels)}"]
        for r in rels.rels:
            out.append(" ".join(map(str, [len(r)] + list(r))))
        self.p.stdin.write("\n".join(out) + "\n"); self.p.stdin.flush()
    def query(self, a, b, maxlen, limit, grow=100):
        a = tuple(a); b = tuple(b)
        self.p.stdin.write(f"0 {maxlen} {limit} {grow} {len(a)} {' '.join(map(str, a))} {len(b)} {' '.join(map(str, b))}\n")
        self.p.stdin.flush()
        head = self.p.stdout.readline().split()
        if head[0] == "FAIL":
            return None
        steps = []
        for _ in range(int(head[1])):
            parts = self.p.stdout.readline().split()
            if parts[0] == "I":
                st = tuple(int(x) for x in parts[1:]); st = (st[0], st[1], st[2], st[3], bool(st[4]))
                steps.append(self.rels.inverse(st))
            else:
                st = tuple(int(x) for x in parts); steps.append((st[0], st[1], st[2], st[3], bool(st[4])))
        assert self.rels.replay(a, steps) == b
        return steps

def lrs_relators():
    R = Relators()
    for g in GENS:
        R.add((GI[g], GI[g]), ("inv", g))
    for (fam, idx, l, r) in T1:
        R.add(tuple(GI[x] for x in l) + tuple(GI[x] for x in reversed(r)), (fam, idx))
    return R

N = lambda a: ('n', a); X = lambda a, b: ('x', a, b); K = lambda *q: ('k',) + q
D = {"X0": [X(3,7), X(2,6), X(1,5), X(0,4)], "X1": [X(5,7), X(4,6), X(1,3), X(0,2)],
     "X2": [X(6,7), X(4,5), X(2,3), X(0,1)], "CX01": [X(5,7), X(4,6)], "CX02": [X(6,7), X(4,5)],
     "CX10": [X(3,7), X(2,6)], "CX12": [X(6,7), X(2,3)], "CX20": [X(3,7), X(1,5)], "CX21": [X(5,7), X(1,3)],
     "CCX01": [X(6,7)], "CCX02": [X(5,7)], "CCX12": [X(3,7)],
     "Z0": [N(4), N(5), N(6), N(7)], "Z1": [N(2), N(3), N(6), N(7)], "Z2": [N(1), N(3), N(5), N(7)],
     "CZ01": [N(6), N(7)], "CZ02": [N(5), N(7)], "CZ12": [N(3), N(7)],
     "K01": [K(0,2,4,6), K(1,3,5,7)], "K12": [K(0,1,2,3), K(4,5,6,7)],
     "S01": [X(3,5), X(2,4)], "S02": [X(3,6), X(1,4)], "S12": [X(5,6), X(1,2)], "Kc": [K(0,1,2,3)], "CCZ": [N(7)]}

if __name__ == "__main__":
    R = lrs_relators()
    S = CSearch7(int(sys.argv[1]) if len(sys.argv) > 1 else 8, R)
    tests = {
      "CZ01": (D["K12"] + D["CX01"] + D["K12"], D["CZ01"]),
      "Z0": (D["CZ01"] + D["CX01"] + D["CZ01"] + D["CX01"], D["Z0"]),
      "Z1": (D["K12"] + D["X1"] + D["K12"], D["Z1"]),
      "Z2": (D["S02"] + D["Z0"] + D["S02"], D["Z2"]),
      "CZ02": (D["S12"] + D["CZ01"] + D["S12"], D["CZ02"]),
      "CZ12": (D["S01"] + D["CZ02"] + D["S01"], D["CZ12"]),
      "K01": (D["S02"] + D["K12"] + D["S02"], D["K01"]),
    }
    import pickle
    found = {}
    for nm, (a, b) in tests.items():
        assert lev(a) == lev(b), nm
        aa = [GI[g] for g in a]; bb = [GI[g] for g in b]
        for ex in (2, 4):
            for g in (1, 2, 100):
                t = time.time()
                st = S.query(aa, bb, min(18, max(len(aa), len(bb)) + ex), 4000000, grow=g)
                print(nm, len(aa), len(bb), ex, g, None if st is None else len(st), round(time.time() - t, 1), flush=True)
                if st is not None:
                    found[nm] = (aa, bb, st); break
            if nm in found: break
    pickle.dump(found, open(work("lrs_found.pkl"), "wb"))
