import sys
sys.path.insert(0, '.')
import core as C
import natproof as NP
gs = C.GateSet(3)
I = gs.index
def W(s): return tuple(I[t] for t in s.split())
ax = NP.axioms(gs)
ccx = I['CCX0']
base = [tuple(a.lhs) + tuple(reversed(a.rhs)) for a in ax if ccx not in tuple(a.lhs) + tuple(a.rhs)]
Z0 = 'HH0 X0 HH0'; Z2 = 'HH1 X2 HH1'
extra = {
    'Z0-CX1': W(f'{Z0} CX1 {Z0} CX1'),
    'Z0-HH1': W(f'{Z0} HH1 {Z0} HH1'),
    'Z2-CX0': W(f'{Z2} CX0 {Z2} CX0'),
    'Z2-HH0': W(f'{Z2} HH0 {Z2} HH0'),
}
sub = [(I[g],) for g in ['X0', 'X1', 'CX0', 'HH0', 'X2']]
import itertools
for k in range(1, 5):
    for names in itertools.combinations(extra, k):
        r = C.index_c(len(gs.names), base + [extra[n] for n in names], sub, limit=3_000_000)
        print(names, r, flush=True)
