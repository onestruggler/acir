from way import *

def lgen(g, ren=None):
    f = (lambda i: ren[i]) if ren else (lambda i: i)
    if g[0] == 'Z': return f"zL {f(g[1])}"
    if g[0] == 'X': return f"xL {f(g[1])} {f(g[2])}"
    if g[0] == 'H': return f"hL {f(g[1])} {f(g[2])}"

def llist(w, ren=None):
    return '[' + ', '.join(lgen(g, ren) for g in w) + ']'

def emit_steps(N, steps, K, extnames):
    out = []
    for s in steps:
        k, pos, W, R = s[:4]
        if k == 'ext':
            name, fwd = s[4], s[5]
            out.append(f".ext {extnames.index(name)} {pos} {'true' if fwd else 'false'}")
            continue
        S = supp(W) | supp(R)
        if k == 'comm' and len(S) > K:
            x, y = W
            kinds = x[0] + y[0]
            if kinds == 'XX': out.append(f".rel .b3 [{x[1]}, {x[2]}, {y[1]}, {y[2]}] {pos} true")
            elif kinds == 'XH': out.append(f".rel .b5 [{x[1]}, {x[2]}, {y[1]}, {y[2]}] {pos} true")
            elif kinds == 'HX': out.append(f".rel .b5 [{y[1]}, {y[2]}, {x[1]}, {x[2]}] {pos} false")
            elif kinds == 'HH': out.append(f".rel .b6 [{x[1]}, {x[2]}, {y[1]}, {y[2]}] {pos} true")
            else: raise ValueError(s)
            continue
        # sem window: choose e = sorted support padded
        e = sorted(S)
        for i in range(N):
            if len(e) >= K: break
            if i not in e: e.append(i)
        e = sorted(e)
        inv = {v: i for i, v in enumerate(e)}
        out.append(f".sem ![{', '.join(map(str, e))}] {llist(W, inv)} {llist(R, inv)} {pos}")
    return out
