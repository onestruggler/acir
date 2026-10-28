import os
HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.join(HERE, '..')
import json
from leanfmt import *
from sides2 import apply_all
from rules import N, K
d = json.load(open(os.path.join(HERE, 'd325.json')))
def T(w): return tuple(tuple(g) for g in w)
K4 = ('k', 0, 1, 2, 3)
def sg(bits): return tuple(N(i) for i in range(4) if bits[i])
B = lambda c: 'true' if c == '1' else 'false'
ev, od = [], []
for key, (V, st) in sorted(d.items()):
    V = T(V); st = [tuple(s) for s in st]
    if key[0] == 'e':
        t = tuple(int(c) for c in key[1:5])
        assert apply_all((K4,), st) == V + (K4,) + sg(t)
        ev.append((key[1:5], V, st))
    else:
        t = tuple(int(c) for c in key[1:5]); t2 = tuple(int(c) for c in key[5:9])
        assert apply_all((K4,) + sg(t2) + (K4,), st) == V + (K4,) + sg(t)
        od.append((key[1:5], key[5:9], V, st))
out = ["""/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Lemma A.20, Subcase 3.2.5: the relations on `0, …, 3`

`K = K_[0,1,2,3]` with the signs `S = (−1)^τ` of a syllable on the four
indices.  When evenly many `τ_i` are set, `K ≈ V K S` (`chk325e`); when oddly
many are set at `s` and at `K s`, `K S' K ≈ V K S` (`chk325o`), with `V` a
word of `(−1)` and `X` letters, as Corollaries A.13 and A.14 assert.  The
chains are found by a search script (scratch) and checked by the kernel.
-/
import QCert.LiRossSelinger.Derive

namespace QCert.LiRossSelinger

open QCert

/-- `K_[0,1,2,3]` on four indices. -/
def K4 : Gen 4 := Gen.k 0 1 2 3 (by decide) (by decide) (by decide)

/-- The signs `(−1)_[0]^{t₀} ⋯ (−1)_[3]^{t₃}` on four indices. -/
def sgn4 (t0 t1 t2 t3 : Bool) : List (Gen 4) := negw t0 0 ++ negw t1 1 ++ negw t2 2 ++ negw t3 3
"""]
def lit(w): return word_lit(w).replace('Gen.k 0 1 2 3 (by decide) (by decide) (by decide)', 'K4')
out.append("/-- The word `V` of `K ≈ V K S` (evenly many signs). -/\ndef V325e : Bool → Bool → Bool → Bool → List (Gen 4)")
for b, V, st in ev:
    out.append(f"  | {', '.join(B(c) for c in b)} => {lit(V)}")
out.append("  | _, _, _, _ => []\n")
out.append("/-- The chains of `K ≈ V K S`. -/\ndef S325e : Bool → Bool → Bool → Bool → List (GStep ((Fam ⊕ MFam) × Bool) 4)")
for b, V, st in ev:
    out.append(f"  | {', '.join(B(c) for c in b)} =>\n    {steps_lit(st, step_d)}")
out.append("  | _, _, _, _ => []\n")
out.append("/-- The word `V` of `K S' K ≈ V K S` (oddly many signs at both). -/\ndef V325o : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool → List (Gen 4)")
for b, b2, V, st in od:
    out.append(f"  | {', '.join(B(c) for c in b + b2)} => {lit(V)}")
out.append("  | _, _, _, _, _, _, _, _ => []\n")
out.append("/-- The chains of `K S' K ≈ V K S`. -/\ndef S325o : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool →\n    List (GStep ((Fam ⊕ MFam) × Bool) 4)")
for b, b2, V, st in od:
    out.append(f"  | {', '.join(B(c) for c in b + b2)} =>\n    {steps_lit(st, step_d)}")
out.append("  | _, _, _, _, _, _, _, _ => []\n")
out.append("""theorem chk325e : ∀ t0 t1 t2 t3 : Bool, (t0 ^^ t1 ^^ t2 ^^ t3) = false →
    checkD [K4] (V325e t0 t1 t2 t3 ++ K4 :: sgn4 t0 t1 t2 t3) (S325e t0 t1 t2 t3) = true := by
  decide +kernel

theorem chk325o : ∀ t0 t1 t2 t3 u0 u1 u2 u3 : Bool, (t0 ^^ t1 ^^ t2 ^^ t3) = true →
    (u0 ^^ u1 ^^ u2 ^^ u3) = true →
    checkD (K4 :: sgn4 u0 u1 u2 u3 ++ [K4]) (V325o t0 t1 t2 t3 u0 u1 u2 u3 ++ K4 :: sgn4 t0 t1 t2 t3)
      (S325o t0 t1 t2 t3 u0 u1 u2 u3) = true := by
  decide +kernel

theorem tag325e : ∀ t0 t1 t2 t3 : Bool, ∀ g ∈ V325e t0 t1 t2 t3, g.tag ≠ 2 := by decide

theorem tag325o : ∀ t0 t1 t2 t3 u0 u1 u2 u3 : Bool, ∀ g ∈ V325o t0 t1 t2 t3 u0 u1 u2 u3,
    g.tag ≠ 2 := by decide

end QCert.LiRossSelinger
""")
open(os.path.join(LEAN, 'Rel325.lean'), 'w', encoding='utf-8', newline='\n').write("\n".join(out))
print(len(ev), len(od))
