import sys
from lat import G, vec
import ss

def perm_group(gens):
    basis = [vec([1 if j == i else 0 for j in range(8)]) for i in range(8)]
    idx = {v: k for k, v in enumerate(basis)}
    pts = list(basis); fr = list(basis)
    while fr:
        new = []
        for v in fr:
            for g in gens:
                w = G[g](v)
                if w not in idx:
                    idx[w] = len(pts); pts.append(w); new.append(w)
        fr = new
        if len(pts) > 100000: raise SystemExit("orbit too big")
    return [tuple(idx[G[g](v)] for v in pts) for g in gens], len(pts)

CL = ["X0","X1","X2","CX01","CX12","CX10","CX21","CX02","CX20"]
if __name__ == "__main__":
    sets = {"<X,CX,HH>": CL + ["HH01","HH12","HH02"], "C3": CL + ["H0","H1","H2"],
            "Theta": CL + ["CCX0","HH01","HH12","HH02"]}
    for name, gens in sets.items():
        perms, n = perm_group(gens)
        print(name, "orbit", n, "order", ss.order(perms), flush=True)
