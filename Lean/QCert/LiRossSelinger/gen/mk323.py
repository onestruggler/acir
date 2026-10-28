import os
HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.join(HERE, '..')
import json
from collections import defaultdict
from leanfmt import *
from sides2 import apply_all
from rules import N, K
d = json.load(open(os.path.join(HERE, 'd323.json')))
def T(w): return tuple(tuple(g) for g in w)
K0124 = ('k', 0, 1, 2, 4)
cfgs = defaultdict(dict)
for key, (P, st) in d.items():
    abab, bits = key.split('_')
    a, b, al, be = map(int, abab)
    x, y, p, q = map(int, bits[:4])
    P = T(P); st = [tuple(s) for s in st]
    i = P.index(K0124)
    Xl, Yl = P[:i], P[i + 1:]
    lhs = (K(al, be, 4, 5),) + ((N(al),) if x else ()) + ((N(be),) if y else ()) + (K(0, 1, 2, 3),)
    rhs = P + (K(a, b, 4, 5),) + ((N(a),) if p else ()) + ((N(b),) if q else ())
    assert apply_all(lhs, st) == rhs
    cfgs[(a, b, al, be)][(x, y, p, q)] = (Xl, Yl, st)
NM = ['a₀', 'a₁', 'a₂', 'a₃', 'c', 'd']
NM2 = ['a0', 'a1', 'a2', 'a3', 'c', 'd']
B = lambda v: 'true' if v else 'false'
out = ["""/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Lemma A.20, Subcase 3.2.3: the relations on `0, …, 3, c, d`

For the first odd entries `a < b ≤ 3 < c < d` of `s` and the two odd entries
`α < β ≤ 3` of `K_[0,1,2,3] s` (twelve configurations, Lemma A.3), and the
signs `x, y, p, q` of `α, β, a, b` (eight patterns of a fixed parity each),

  `K_[α,β,c,d] (−1)_[α]^x (−1)_[β]^y K_[0,1,2,3] ≈ X K_[0,1,2,c] Y K_[a,b,c,d] (−1)_[a]^p (−1)_[b]^q`

with `X`, `Y` words of `(−1)` and `X` letters (Proposition A.15).  Each is
reduced to the one instance of (5a) on `0, 1, 2, 3, c, d`,
`K_[0,1,2,3] K_[1,3,c,d] ≈ K_[2,3,c,d] K_[0,1,2,c]`, by moving signed
permutations through the `K`s; the chains are found by a search script
(scratch), checked by the kernel on `0, …, 5` and moved along an order
embedding.
-/
import QCert.LiRossSelinger.Derive
import QCert.LiRossSelinger.PathSP

namespace QCert.LiRossSelinger

open QCert

variable {n : ℕ}
"""]
def lit(w): return word_lit(w)
for (a, b, al, be), cases in sorted(cfgs.items()):
    tag = f"{a}{b}{al}{be}"
    pars = {x ^ y ^ p ^ q for (x, y, p, q) in cases}
    assert len(pars) == 1 and len(cases) == 8
    par = pars.pop()
    out.append(f"/-- `X` for `{{a,b}} = {{{a},{b}}}`, `{{α,β}} = {{{al},{be}}}`. -/\ndef X323_{tag} : Bool → Bool → Bool → Bool → List (Gen 6)")
    for bits, (Xl, Yl, st) in sorted(cases.items()):
        out.append(f"  | {', '.join(B(v) for v in bits)} => {lit(Xl)}")
    out.append("  | _, _, _, _ => []\n")
    out.append(f"/-- `Y` for `{{a,b}} = {{{a},{b}}}`, `{{α,β}} = {{{al},{be}}}`. -/\ndef Y323_{tag} : Bool → Bool → Bool → Bool → List (Gen 6)")
    for bits, (Xl, Yl, st) in sorted(cases.items()):
        out.append(f"  | {', '.join(B(v) for v in bits)} => {lit(Yl)}")
    out.append("  | _, _, _, _ => []\n")
    out.append(f"/-- The chains for `{{a,b}} = {{{a},{b}}}`, `{{α,β}} = {{{al},{be}}}`. -/\ndef S323_{tag} : Bool → Bool → Bool → Bool → List (GStep ((Fam ⊕ MFam) × Bool) 6)")
    for bits, (Xl, Yl, st) in sorted(cases.items()):
        out.append(f"  | {', '.join(B(v) for v in bits)} =>\n    {steps_lit(st, step_d)}")
    out.append("  | _, _, _, _ => []\n")
    kl = lit([K(al, be, 4, 5)])[1:-1]
    kr = lit([K(a, b, 4, 5)])[1:-1]
    k0 = lit([K(0, 1, 2, 3)])[1:-1]
    k4 = lit([K0124])[1:-1]
    out.append(f"""theorem chk323_{tag} : ∀ x y p q : Bool, xor (xor (xor x y) p) q = {B(par)} →
    checkD ({kl} :: (negw x {al} ++ negw y {be}) ++ [{k0}])
      (X323_{tag} x y p q ++ {k4} :: Y323_{tag} x y p q ++
        {kr} :: (negw p {a} ++ negw q {b})) (S323_{tag} x y p q) = true := by
  decide +kernel

theorem tag323_{tag} : ∀ x y p q : Bool, ∀ g ∈ X323_{tag} x y p q ++ Y323_{tag} x y p q, g.tag ≠ 2 := by
  decide
""")
    sym = lambda w: word_sym(w, NM2)[1:-1]
    hy = "(h1 : a0 < a1) (h2 : a1 < a2) (h3 : a2 < a3) (h4 : a3 < c) (h5 : c < d)"
    out.append(f"""/-- Subcase 3.2.3 with `{{a,b}} = {{{a},{b}}}`, `{{α,β}} = {{{al},{be}}}` (from `0`). -/
theorem rel323_{tag} {{a0 a1 a2 a3 c d : Fin n}} {hy} (x y p q : Bool)
    (hpar : xor (xor (xor x y) p) q = {B(par)}) :
    ∃ Xw Yw : List (Gen n), (∀ g ∈ Xw ++ Yw, g.tag ≠ 2 ∧ extent g ≤ d.val) ∧
      Derivable (Table1 n)
        (FreeMonoid.ofList ({sym([K(al, be, 4, 5)])} :: (negw x {NM2[al]} ++ negw y {NM2[be]}) ++
          [{sym([K(0, 1, 2, 3)])}]))
        (FreeMonoid.ofList (Xw ++ {sym([K0124])} :: Yw ++
          {sym([K(a, b, 4, 5)])} :: (negw p {NM2[a]} ++ negw q {NM2[b]}))) := by
  refine ⟨(X323_{tag} x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)),
    (Y323_{tag} x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)), ?_, ?_⟩
  · intro g hg
    rw [← List.map_append] at hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    refine ⟨by rw [tag_rename]; exact tag323_{tag} x y p q g' hg', ?_⟩
    have := extent_rename_le (emb6 h1 h2 h3 h4 h5) g' 5 (extent_le_last g')
    rwa [emb6_5] at this
  · have hh := derivable_rename (emb6 h1 h2 h3 h4 h5) (checkD_sound (chk323_{tag} x y p q hpar))
    rw [renW_ofList, renW_ofList] at hh
    convert hh using 2 <;>
      simp only [List.map_append, List.map_cons, List.map_nil, negw_rename, Gen.rename, emb6_0,
        emb6_1, emb6_2, emb6_3, emb6_4, emb6_5, List.cons_append, List.nil_append,
        List.append_assoc]
""")
out.append("end QCert.LiRossSelinger\n")
open(os.path.join(LEAN, 'Rel323.lean'), 'w', encoding='utf-8', newline='\n').write("\n".join(out))
print(sorted(cfgs), [(k, {x^y^p^q for (x,y,p,q) in v}) for k, v in sorted(cfgs.items())])
