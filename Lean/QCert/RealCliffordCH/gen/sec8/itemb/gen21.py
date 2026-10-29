import pickle
from emit import *
from simlean import run
full, E, st = pickle.load(open('c21.pkl','rb'))
Lw, Rw = full[0], full[-1]
assert run(6, 5, [(E[0][1], E[0][2])], st, Lw) == Rw
out = []
out.append(f"/-- Clément's (21) at `0, …, 5`, over `𝒢₆`. -/")
out.append(f"def c21L : List (Gen 6) := {llist(Lw)}")
out.append(f"/-- The right-hand side. -/")
out.append(f"def c21R : List (Gen 6) := {llist(Rw)}")
out.append(f"/-- The relation of (46) at `0, …, 5`, the one extra equation. -/")
out.append(f"def e46E : List (List (Gen 6) × List (Gen 6)) :=\n  [({llist(E[0][1])},\n    {llist(E[0][2])})]")
out.append(f"/-- The chain. -/")
body = ',\n  '.join(st)
out.append(f"def ch21 : List (CS 6 5) := [\n  {body}]")
out.append(f"theorem run21 : run e46E ch21 c21L = some c21R := by decide +kernel")
open('c21.lean.txt','w',encoding='utf-8').write('\n'.join(out))
print(len(st)); print('\n'.join(out)[:3000])
