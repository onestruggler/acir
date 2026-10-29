from way import *
import pickle, time
lib = build_lib(4, 3, 3)
txt = open('../rcch/paper.txt', encoding='utf-8').read().split('\n')[2696:2760]
lines = [parse(l) for l in txt if l.startswith('𝐻')]
L,R = d3(0,1,2,3)
lines=[L]+lines+[[H(0,1),H(2,3)]]
# waypoints for 10: push block
u,v = lines[10], lines[11]
p,q = strip(u,v)
mid = u[p:len(u)-q]  # Z2 Z3 Z0 Z1 H02 H13 H23 H02 H13
blk, hs = mid[:4], mid[4:]
wps = [u[:p] + hs[:k] + blk + hs[k:] + u[len(u)-q:] for k in range(1, len(hs))]
# waypoints for 16: cancellation of the middle
u2,v2 = lines[16], lines[17]
p2,q2 = strip(u2,v2)
mid2 = u2[p2:len(u2)-q2]
wps2 = [u2[:p2] + w + u2[len(u2)-q2:] for w in cancel_waypoints(mid2)][:-1]
full = lines[:11] + wps + lines[11:17] + wps2 + lines[17:]
print(len(full))
t=time.time()
steps, bad = solve_chain(4, full, lib, 3, rules=[('d20', L20, R20)], depth=4)
print('steps', None if steps is None else len(steps), 'time', round(time.time()-t,1))
if steps: pickle.dump((full, steps), open('d3A.pkl','wb'))
