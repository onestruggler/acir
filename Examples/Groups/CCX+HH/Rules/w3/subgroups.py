import sys
sys.path.insert(0, '..')
import core as C
from ss import order
gs = C.GateSet(3); rep = C.PermRep(gs)
for name, letters in [
    ('W(E8)', ['X0','X1','X2','CX0','CX1','CCX0','HH0','HH1']),
    ('Q=<X,CX,HH>', ['X0','X1','X2','CX0','CX1','HH0','HH1']),
    ('classical', ['X0','X1','X2','CX0','CX1','CCX0']),
    ('2-wire {0,1}', ['X0','X1','CX0','HH0']),
    ('<X,CX,CCX,HH0>', ['X0','X1','X2','CX0','CX1','CCX0','HH0']),
]:
    print(name, order([rep.gens[gs.index[l]] for l in letters]))
