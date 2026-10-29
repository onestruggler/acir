import pickle
from emit import *
from simlean import run
res = pickle.load(open('d3gen.pkl','rb'))
out = []
for name in ('A','B'):
    Lw, Rw, E, st = res[name]
    assert run(4, 3, [(E[0][1], E[0][2])], st, Lw) == Rw
    out.append(f"/-- (d3), shape {name}: the two sides. -/")
    out.append(f"def d3L{name} : List (Gen 4) := {llist(Lw)}")
    out.append(f"/-- The right-hand side. -/")
    out.append(f"def d3R{name} : List (Gen 4) := {llist(Rw)}")
    out.append(f"/-- Clément's (20) at the indices the chain uses. -/")
    out.append(f"def e20{name} : List (List (Gen 4) × List (Gen 4)) :=\n  [({llist(E[0][1])},\n    {llist(E[0][2])})]")
    out.append(f"/-- The chain. -/")
    body = ',\n  '.join(st)
    out.append(f"def ch{name} : List (CS 4 3) := [\n  {body}]")
    out.append(f"theorem run{name} : run e20{name} ch{name} d3L{name} = some d3R{name} := by decide +kernel")
    out.append("")
open('d3chains.lean.txt','w',encoding='utf-8').write('\n'.join(out))
print('ok', sum(len(res[k][3]) for k in res))
