"""Is Q = <X, CX, HH> on three wires presented by the natural rules that
use only its letters?  Enumerate cosets of A = <X0 X1 CX0 HH0 X2>."""
import sys
sys.path.insert(0, '.')
import core as C
import natproof as NP
gs = C.GateSet(3)
ax = NP.axioms(gs)
ccx = gs.index['CCX0']
rels = []
for a in ax:
    rel = tuple(a.lhs) + tuple(reversed(a.rhs))
    if ccx in rel:
        continue
    rels.append(rel)
print('relators without CCX', len(rels), [a.name for a in ax if ccx not in tuple(a.lhs)+tuple(a.rhs)])
sub = [(gs.index[g],) for g in ['X0', 'X1', 'CX0', 'HH0', 'X2']]
for lim in (2_000_000, 20_000_000):
    print('limit', lim, 'index', C.index_c(len(gs.names), rels, sub, limit=lim), flush=True)
