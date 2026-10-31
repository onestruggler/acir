"""Checked frame factorizations for the four-point Hadamard equation."""
from permutation_normalize import *
from emit_permutation_frames import chunks,fl,gray_word
data=json.loads((Path(__file__).parent/'data/permutation_natural.json').read_text())
tn=data['tokens'];gn=data['gates']
def expand(w):return sum((tn[i]for i in w),[])
out=['''/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Frames for the controlled Hadamard blocks
-/
import QCert.CliffordCS3.Three.PermutationRoutes

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QCert.CliffordCS3.Three.PermutationBlockFrames
open PermutationRoutes PermutationNatural
''']
cases=[('horizontal',[4,5,6,4,5],['CX12'],'W.CX12'),
       ('vertical_right',[4,5],['S02'],'PermutationBase.swap02'),
       ('vertical_left',[6,5],['CX10','S02'],'W.CX10 * PermutationBase.swap02')]
for name,F,gates,target in cases:
    nw=sum((gn[g]for g in gates),[])
    sw=gray_word(permutation(expand(F[::-1])+nw));assert all(i<5 for i in sw),(name,sw)
    l=expand(F+sw);r=nw;nl,sl=normalize(l);nr,sr=normalize(r);assert nl==nr
    st=sl+[(p,k,not rev)for p,k,rev in reversed(sr)]
    proof='gate_'+gates[-1]
    for g in reversed(gates[:-1]):proof=f'(gate_{g}).mul ({proof})'
    out.append(f'''def {name}_frame : List (Fin 7) := {fl(F)}
def {name}_stabilizer : List (Fin 7) := {fl(sw)}

theorem {name}_bound : ∀ d ∈ {name}_stabilizer, d.val < 5 := by decide

theorem {name} : Derivable Rel (tokens ({name}_frame ++ {name}_stabilizer)) ({target}) := by
  have hr : Derivable Rel ({target}) (NW {fl(r)}) := by
    simpa only [NW, FreeMonoid.ofList_append, map_mul, mul_assoc] using ({proof})
  exact (tokens_eq ({name}_frame ++ {name}_stabilizer)).trans
    ((derive {fl(l)} {fl(r)} {chunks(st)} (by decide +kernel)).trans hr.symm)
''')
    print(name,sw)
out.append('end QCert.CliffordCS3.Three.PermutationBlockFrames\n')
path=ROOT/'CliffordCS3/Three/PermutationBlockFrames.lean';path.write_text('\n\n'.join(out),encoding='utf8')
