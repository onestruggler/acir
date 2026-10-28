from itertools import permutations, combinations
from model import table1
def sw(j, i): return j+1 if i == j else (j if i == j+1 else i)
def act(j, g): return (g[0],) + tuple(sw(j, i) for i in g[1:])
def valid(j, g): return not (j in g[1:] and j+1 in g[1:])
def actPath(P, g):
    for j in P: g = act(j, g)
    return g
def validPath(P, g):
    for j in P:
        if not valid(j, g): return False
        g = act(j, g)
    return True
def arrange(s, t):
    free = [p for p in range(8) if p not in s]
    freeT = [p for p in range(8) if p not in t]
    out = []
    for p in range(8):
        if p in s: out.append(t[s.index(p)])
        else: out.append(freeT[free.index(p)])
    return out
def pass_(l, i):
    if len(l) >= 2:
        a, b = l[0], l[1]
        if b < a:
            r, s = pass_([a] + l[2:], i+1); return [b] + r, [i] + s
        r, s = pass_([b] + l[2:], i+1); return [a] + r, s
    return l, []
def bubble(n, l):
    out = []
    for _ in range(n):
        l, s = pass_(l, 0); out += s
    return out
def path(s, t): return bubble(8, arrange(s, t))
def palPath(a, b): return list(range(a, b)) + list(range(a, b-1))[::-1]
STD = {"1b": (0,), "1c": (0,1,2,3), "2d": (0,4), "2e": (4,0,1,2,3), "2f": (0,1,2,3,4,5,6,7),
       "4a": (0,1,2,3), "4b": (0,1,2,3), "4c": (0,1,2,3), "5a": (0,1,2,3,4,5), "6a": tuple(range(8))}
R = table1()
std_inst = {}
for fam, idx, l, r in R:
    if fam in STD and idx == STD[fam]: std_inst[fam] = (l, r)
bad = 0; maxlen = 0
for fam, idx, l, r in R:
    if fam in STD:
        P = path(list(STD[fam]), list(idx))
        maxlen = max(maxlen, len(P))
        L0, R0 = std_inst[fam]
        ok = all(validPath(P, g) for g in L0 + R0) and [actPath(P, g) for g in L0] == l and [actPath(P, g) for g in R0] == r
    else:
        # palindromic: first generator of lhs is X_[a,b], second g; rhs = [g', X_[a,b]] or [] for 1a
        if fam == "1a":
            ok = True
        else:
            xg, g = l[0], l[1]
            P = palPath(xg[1], xg[2])
            ok = validPath(P, g) and r == [actPath(P, g), xg]
    if not ok:
        bad += 1; print("BAD", fam, idx)
print("bad", bad, "max path", maxlen)
