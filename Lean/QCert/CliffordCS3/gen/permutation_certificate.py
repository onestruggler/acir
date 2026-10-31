"""Transport the independently checked Lean permutation certificates."""
import json, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
p = json.loads((ROOT / 'ToffoliHadamard/gen/data/micro.json').read_text())
names = p['names']
used = set()
LET = ['X0','X1','X2','CX01','CX02','CX10','CX12','CX20','CX21',
       'CCX01','CCX02','CCX12','Z0','Z1','Z2','CZ01','CZ02','CZ12',
       'K01','K12','S01','S02','S12','Kc','CCZ']
pure = LET[:12] + LET[20:23]
stack = [i for i,n in enumerate(names) if n.startswith('far') or n.startswith('braid')
         or n in ['route_' + x for x in pure]]
targets = [names[i] for i in stack]
while stack:
    i = stack.pop()
    if i in used:
        continue
    used.add(i)
    d = p['der'][i]
    if d is not None:
        stack += [x[1] for x in d[2]]
print(targets)
print([(i,names[i]) for i in sorted(used) if p['der'][i] is None])
print(len(used))

def wl(w): return '[' + ', '.join('Sym1.' + LET[x] for x in w) + ']'
def pack(steps):
    v = 0
    for i,k,r,c,b in reversed(steps):
        v = v * 17592186044416 + i * 8589934592 + k * 524288 + r * 1024 + c * 2 + int(b)
    return v

sys.set_int_max_str_digits(0)
out=['''/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Kernel replay of the permutation equations

The proof DAG is the independent Lean Toffoli-Hadamard development's
permutation calculation, with its required Figure 4 equations proved
inside the Clifford+CS syntactic quotient.
-/
import QCert.CliffordCS3.Three.PermutationTransport
import QCert.ToffoliHadamard.Engine

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QCert.CliffordCS3.Three.PermutationCert
open ToffoliHadamard ToffoliHadamard.Engine
open PermutationBase

def R : WRel Sym1 := fun a b => Derivable Rel (D a) (D b)

theorem transfer {a b : Word Sym1} (h : Derivable R a b) : Derivable Rel (D a) (D b) :=
  Derivable.map D (fun _ _ h => h) h

theorem involutions (g : Sym1) : Derivable R (FreeMonoid.ofList [g,g]) 1 :=
  Derivable.of (generator_involution g)

def replay (E : List (Rule R)) (l r : List Sym1) (n code : Nat)
    (hc : rrun (E.map fun e => (e.lhs, e.rhs)) l (decodeRot n code) = some r) : Rule R where
  lhs := l
  rhs := r
  sound := rrun_sound involutions (by
    intro e he
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
    exact x.sound) hc
''']
sys.path.insert(0, str(ROOT / 'ToffoliHadamard/gen'))
from rels import FIG4
fig = {f'r{n}': ([LET.index(x) for x in l],[LET.index(x) for x in r]) for n,l,r in FIG4}
for rid in sorted(used):
    n=names[rid];d=p['der'][rid]
    if d is None:
        if n.startswith('inv_'):
            x=n[4:]
            out.append(f'def r{rid} : Rule R := Rule.ofDerivable _ _ (involutions .{x})')
        else:
            l,r=fig[n]
            out.append(f'def r{rid} : Rule R := Rule.ofDerivable (FreeMonoid.ofList {wl(l)})\n  (FreeMonoid.ofList {wl(r)}) (Derivable.of PermutationBase.{n})')
    else:
        l,r,st=d;deps=sorted(set(x[1] for x in st));dmap={v:i for i,v in enumerate(deps)}
        st=[(i,dmap[k],rot,cut,rv) for i,k,rot,cut,rv in st]
        out.append(f'def r{rid} : Rule R := replay [{", ".join("r"+str(i) for i in deps)}]\n  {wl(l)} {wl(r)}\n  {len(st)} {pack(st)} (by decide +kernel)')
for n in targets:
    i=names.index(n)
    l,r=p['der'][i][:2]
    out.append(f'theorem {n} : PermutationBase.Eqn {wl(l)} {wl(r)} := transfer r{i}.sound')
out.append('end QCert.CliffordCS3.Three.PermutationCert\n')
path=ROOT/'CliffordCS3/Three/PermutationCert.lean'
path.write_text('\n\n'.join(out),encoding='utf8')
