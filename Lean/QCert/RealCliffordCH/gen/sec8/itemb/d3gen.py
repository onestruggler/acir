from emit import *
import pickle, sys
lib = build_lib(4, 3, 3)
txt = open('../rcch/paper.txt', encoding='utf-8').read().split('\n')[2696:2760]
lines0 = [parse(l) for l in txt if l.startswith('𝐻')]
L,R = d3(0,1,2,3)
lines0=[L]+lines0+[[H(0,1),H(2,3)]]
def build(lines):
    u,v = lines[10], lines[11]
    p,q = strip(u,v); mid = u[p:len(u)-q]; blk, hs = mid[:4], mid[4:]
    wps = [u[:p] + hs[:k] + blk + hs[k:] + u[len(u)-q:] for k in range(1, len(hs))]
    u2,v2 = lines[16], lines[17]
    p2,q2 = strip(u2,v2); mid2 = u2[p2:len(u2)-q2]
    wps2 = [u2[:p2] + w + u2[len(u2)-q2:] for w in cancel_waypoints(mid2)][:-1]
    return lines[:11] + wps + lines[11:17] + wps2 + lines[17:]
res = {}
for name, perm in (('A', {0:0,1:1,2:2,3:3}), ('B', {0:0,1:2,2:1,3:3})):
    lines = [ren(perm, w) for w in lines0]
    full = build(lines)
    E = [('d20', ren(perm, L20), ren(perm, R20))]
    steps, bad = solve_chain(4, full, lib, 3, rules=E, depth=4)
    print(name, len(steps))
    res[name] = (full[0], full[-1], E, emit_steps(4, steps, 3, ['d20']))
pickle.dump(res, open('d3gen.pkl', 'wb'))
for name in res:
    Lw, Rw, E, st = res[name]
    print(name, llist(Lw), llist(Rw), llist(E[0][1]), llist(E[0][2]))
    print(st[:5])
