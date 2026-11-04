/-
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

/-- (6a), as `W⁻¹ C W ≈ C`. -/
theorem rel1223_e {a b c d e f g h : Fin n} (h1 : a < b) (h2 : b < c) (h3 : c < d) (h4 : d < e)
    (h5 : e < f) (h6 : f < g) (h7 : g < h) :
    Derivable (Table1 n) (FreeMonoid.ofList [Gen.x a e (h1.trans (h2.trans (h3.trans h4))), Gen.neg e, Gen.neg a, Gen.k a b c d h1 h2 h3, Gen.k e f g h h5 h6 h7, Gen.x d e h4, Gen.k e f g h h5 h6 h7, Gen.k a b c d h1 h2 h3, Gen.neg a, Gen.neg e, Gen.x a e (h1.trans (h2.trans (h3.trans h4)))])
      (FreeMonoid.ofList [Gen.k e f g h h5 h6 h7, Gen.k a b c d h1 h2 h3, Gen.x d e h4, Gen.k a b c d h1 h2 h3, Gen.k e f g h h5 h6 h7]) := by
  have hh := derivable_rename (emb8 h1 h2 h3 h4 h5 h6 h7) (checkD_sound
    (w := ([Gen.x 0 4 (by decide), Gen.neg 4, Gen.neg 0, Gen.k 0 1 2 3 (by decide) (by decide) (by decide), Gen.k 4 5 6 7 (by decide) (by decide) (by decide), Gen.x 3 4 (by decide), Gen.k 4 5 6 7 (by decide) (by decide) (by decide), Gen.k 0 1 2 3 (by decide) (by decide) (by decide), Gen.neg 0, Gen.neg 4, Gen.x 0 4 (by decide)] : List (Gen 8)))
    (w' := [Gen.k 4 5 6 7 (by decide) (by decide) (by decide), Gen.k 0 1 2 3 (by decide) (by decide) (by decide), Gen.x 3 4 (by decide), Gen.k 0 1 2 3 (by decide) (by decide) (by decide), Gen.k 4 5 6 7 (by decide) (by decide) (by decide)])
    (sts := stepsOf 8 [148868987683720, 73811284526728, 5308678, 5308491, 5308811, 5308422, 5310598, 5310731,
      5310667, 148868987682964])
    (by decide +kernel))
  simpa only [renW_ofList, List.map_cons, List.map_nil, Gen.rename, emb8_0, emb8_1, emb8_2,
    emb8_3, emb8_4, emb8_5, emb8_6, emb8_7] using hh

/-- Proposition A.16, as `W⁻¹ C W ≈ C`. -/
theorem rel1223_h {a b c d e f g h : Fin n} (h1 : a < b) (h2 : b < c) (h3 : c < d) (h4 : d < e)
    (h5 : e < f) (h6 : f < g) (h7 : g < h) :
    Derivable (Table1 n) (FreeMonoid.ofList [Gen.x a h (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7)))))), Gen.neg h, Gen.neg a, Gen.k a b c d h1 h2 h3, Gen.k e f g h h5 h6 h7, Gen.x d e h4, Gen.k e f g h h5 h6 h7, Gen.k a b c d h1 h2 h3, Gen.neg a, Gen.neg h, Gen.x a h (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7))))))])
      (FreeMonoid.ofList [Gen.k e f g h h5 h6 h7, Gen.k a b c d h1 h2 h3, Gen.x d e h4, Gen.k a b c d h1 h2 h3, Gen.k e f g h h5 h6 h7]) := by
  have hh := derivable_rename (emb8 h1 h2 h3 h4 h5 h6 h7) (checkD_sound
    (w := ([Gen.x 0 7 (by decide), Gen.neg 7, Gen.neg 0, Gen.k 0 1 2 3 (by decide) (by decide) (by decide), Gen.k 4 5 6 7 (by decide) (by decide) (by decide), Gen.x 3 4 (by decide), Gen.k 4 5 6 7 (by decide) (by decide) (by decide), Gen.k 0 1 2 3 (by decide) (by decide) (by decide), Gen.neg 0, Gen.neg 7, Gen.x 0 7 (by decide)] : List (Gen 8)))
    (w' := [Gen.k 4 5 6 7 (by decide) (by decide) (by decide), Gen.k 0 1 2 3 (by decide) (by decide) (by decide), Gen.x 3 4 (by decide), Gen.k 0 1 2 3 (by decide) (by decide) (by decide), Gen.k 4 5 6 7 (by decide) (by decide) (by decide)])
    (sts := stepsOf 8 [148868987683720, 73811284526728, 8454406, 8717056, 8717003, 25493764, 5309062, 139526154,
      8456838, 8456971, 8456907, 8719616, 8719563, 25496324, 139528714, 5311307,
      5311627, 5311238, 2271544472, 141952266, 141952265, 8783488, 18020239239, 18020173447,
      288324191621, 122947588, 106170116, 1417021059, 18020239751, 18020173959, 288324192133, 7735371,
      7735691, 7735302, 2271546005, 2271545499, 7735936, 8718720, 5308934, 5308747,
      5309067, 5308678, 5310854, 5310987, 5310923, 148868987683220, 2271543448, 141951242,
      141951241, 8782464, 18020238215, 18020172423, 288324190597, 122946564, 106169092, 1417020035,
      18020238727, 18020172935, 288324191109, 7734347, 7734667, 7734278, 2271544981, 2271544475,
      7734912, 8717696])
    (by decide +kernel))
  simpa only [renW_ofList, List.map_cons, List.map_nil, Gen.rename, emb8_0, emb8_1, emb8_2,
    emb8_3, emb8_4, emb8_5, emb8_6, emb8_7] using hh

end QCert.LiRossSelinger
