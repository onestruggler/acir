import os
HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.join(HERE, '..')
import json
from leanfmt import *
from sides2 import apply_all
d = json.load(open(os.path.join(HERE, 'd1223.json')))
NAMES = list('abcdefgh')
def T(w): return tuple(tuple(g) for g in w)
C = (('k', 4, 5, 6, 7), ('k', 0, 1, 2, 3), ('x', 3, 4), ('k', 0, 1, 2, 3), ('k', 4, 5, 6, 7))
out = ["""/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Lemma A.20, Subcase 1.2.2.3 with `u_e` odd: the two relations

With `C = K_[e,f,g,h] K_[a,b,c,d] X_[d,e] K_[a,b,c,d] K_[e,f,g,h]`, both diagrams of
the paper close by `W⁻¹ C W ≈ C`: for `W = (−1)_[a] (−1)_[e] X_[a,e]` this is
relation (6a) (`rel1223_e`), for `W = (−1)_[a] (−1)_[h] X_[a,h]` Proposition A.16
(`rel1223_h`).  The printed proof of Proposition A.16 derives the relation for
`K_[e,f,g,h] K_[a,b,c,d] K_[a,b,c,e] K_[d,f,g,h]` instead of `C` (it equals
`C X_[d,e]`); here it is (6a) conjugated by `X_[e,h]`, which commutes with `C`
by (8b) at `e, f, g, h`.  Chains on `0, …, 7` found by a search script
(scratch), moved along an order embedding.
-/
import QCert.LiRossSelinger.Derive

namespace QCert.LiRossSelinger

open QCert

variable {n : ℕ}
"""]
for nm, tag, doc in (('D0', 'e', '(6a)'), ('D8', 'h', 'Proposition A.16')):
    l, st = d[nm]
    l = T(l); st = [tuple(s) for s in st]
    assert apply_all(l, st) == C
    out.append(f"""/-- {doc}, as `W⁻¹ C W ≈ C`. -/
theorem rel1223_{tag} {{a b c d e f g h : Fin n}} (h1 : a < b) (h2 : b < c) (h3 : c < d) (h4 : d < e)
    (h5 : e < f) (h6 : f < g) (h7 : g < h) :
    Derivable (Table1 n) (FreeMonoid.ofList {word_sym(l, NAMES)})
      (FreeMonoid.ofList {word_sym(C, NAMES)}) := by
  have hh := derivable_rename (emb8 h1 h2 h3 h4 h5 h6 h7) (checkD_sound
    (w := ({word_lit(l)} : List (Gen 8)))
    (w' := {word_lit(C)})
    (sts := {steps_lit(st, step_d)})
    (by decide +kernel))
  simpa only [renW_ofList, List.map_cons, List.map_nil, Gen.rename, emb8_0, emb8_1, emb8_2,
    emb8_3, emb8_4, emb8_5, emb8_6, emb8_7] using hh
""")
out.append("end QCert.LiRossSelinger\n")
open(os.path.join(LEAN, 'Rel1223.lean'), 'w', encoding='utf-8', newline='\n').write("\n".join(out))
