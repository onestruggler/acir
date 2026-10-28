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
    (sts := [⟨(.inl .r2f, false), [0, 1, 2, 3, 4, 5, 6, 7], true, 3⟩, ⟨(.inl .r2f, false), [4, 5, 6, 7, 0, 1, 2, 3], true, 6⟩, ⟨(.inl .r2d, false), [0, 4], false, 1⟩, ⟨(.inl .r3c, true), [0, 4], false, 0⟩,
      ⟨(.inl .r3c, false), [0, 4], true, 1⟩, ⟨(.inl .r2d, false), [0, 4], false, 0⟩, ⟨(.inl .r2d, false), [0, 4], true, 8⟩, ⟨(.inl .r3c, false), [0, 4], false, 9⟩,
      ⟨(.inl .r3c, true), [0, 4], true, 8⟩, ⟨(.inl .r6a, false), [0, 1, 2, 3, 4, 5, 6, 7], true, 0⟩])
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
    (sts := [⟨(.inl .r2f, false), [0, 1, 2, 3, 4, 5, 6, 7], true, 3⟩, ⟨(.inl .r2f, false), [4, 5, 6, 7, 0, 1, 2, 3], true, 6⟩, ⟨(.inl .r2d, false), [0, 7], false, 1⟩, ⟨(.inl .r1a, false), [4, 7], false, 3⟩,
      ⟨(.inl .r3c, true), [4, 7], true, 2⟩, ⟨(.inl .r2b, false), [4, 7, 0], false, 1⟩, ⟨(.inl .r2d, false), [0, 4], true, 2⟩, ⟨(.inl .r3b, false), [0, 4, 7], false, 0⟩,
      ⟨(.inl .r2d, false), [0, 7], true, 10⟩, ⟨(.inl .r3c, false), [0, 7], false, 11⟩, ⟨(.inl .r3c, true), [0, 7], true, 10⟩, ⟨(.inl .r1a, false), [4, 7], false, 13⟩,
      ⟨(.inl .r3c, true), [4, 7], true, 12⟩, ⟨(.inl .r2b, false), [4, 7, 0], false, 11⟩, ⟨(.inl .r3b, false), [0, 4, 7], false, 10⟩, ⟨(.inl .r3c, true), [0, 4], false, 11⟩,
      ⟨(.inl .r3c, false), [0, 4], true, 12⟩, ⟨(.inl .r2d, false), [0, 4], false, 11⟩, ⟨(.inr .ksym5, false), [4, 5, 6, 7], true, 4⟩, ⟨(.inl .r3b, false), [5, 6, 7], false, 5⟩,
      ⟨(.inl .r3a, false), [5, 6, 7], false, 5⟩, ⟨(.inl .r1a, false), [5, 7], true, 6⟩, ⟨(.inl .r2e, false), [6, 0, 1, 2, 3], true, 7⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 6⟩,
      ⟨(.inl .r2c, false), [5, 6, 0, 1, 2, 3], true, 5⟩, ⟨(.inl .r2b, false), [3, 4, 6], false, 8⟩, ⟨(.inl .r2b, false), [3, 4, 5], false, 7⟩, ⟨(.inl .r2a, false), [5, 6, 3, 4], true, 6⟩,
      ⟨(.inl .r2e, false), [6, 0, 1, 2, 3], true, 9⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 8⟩, ⟨(.inl .r2c, false), [5, 6, 0, 1, 2, 3], true, 7⟩, ⟨(.inl .r3c, true), [5, 6], false, 8⟩,
      ⟨(.inl .r3c, false), [5, 6], true, 9⟩, ⟨(.inl .r2d, false), [5, 6], false, 8⟩, ⟨(.inr .ksym2, false), [4, 5, 6, 7], true, 10⟩, ⟨(.inr .k31, false), [4, 5, 6, 7], true, 8⟩,
      ⟨(.inl .r1a, false), [5, 6], true, 10⟩, ⟨(.inl .r1a, false), [4, 7], true, 9⟩, ⟨(.inl .r2d, false), [0, 4], false, 2⟩, ⟨(.inl .r3c, true), [0, 4], false, 1⟩,
      ⟨(.inl .r3c, false), [0, 4], true, 2⟩, ⟨(.inl .r2d, false), [0, 4], false, 1⟩, ⟨(.inl .r2d, false), [0, 4], true, 9⟩, ⟨(.inl .r3c, false), [0, 4], false, 10⟩,
      ⟨(.inl .r3c, true), [0, 4], true, 9⟩, ⟨(.inl .r6a, false), [0, 1, 2, 3, 4, 5, 6, 7], true, 1⟩, ⟨(.inr .ksym5, false), [4, 5, 6, 7], true, 0⟩, ⟨(.inl .r3b, false), [5, 6, 7], false, 1⟩,
      ⟨(.inl .r3a, false), [5, 6, 7], false, 1⟩, ⟨(.inl .r1a, false), [5, 7], true, 2⟩, ⟨(.inl .r2e, false), [6, 0, 1, 2, 3], true, 3⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 2⟩,
      ⟨(.inl .r2c, false), [5, 6, 0, 1, 2, 3], true, 1⟩, ⟨(.inl .r2b, false), [3, 4, 6], false, 4⟩, ⟨(.inl .r2b, false), [3, 4, 5], false, 3⟩, ⟨(.inl .r2a, false), [5, 6, 3, 4], true, 2⟩,
      ⟨(.inl .r2e, false), [6, 0, 1, 2, 3], true, 5⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 4⟩, ⟨(.inl .r2c, false), [5, 6, 0, 1, 2, 3], true, 3⟩, ⟨(.inl .r3c, true), [5, 6], false, 4⟩,
      ⟨(.inl .r3c, false), [5, 6], true, 5⟩, ⟨(.inl .r2d, false), [5, 6], false, 4⟩, ⟨(.inr .ksym2, false), [4, 5, 6, 7], true, 6⟩, ⟨(.inr .k31, false), [4, 5, 6, 7], true, 4⟩,
      ⟨(.inl .r1a, false), [5, 6], true, 6⟩, ⟨(.inl .r1a, false), [4, 7], true, 5⟩])
    (by decide +kernel))
  simpa only [renW_ofList, List.map_cons, List.map_nil, Gen.rename, emb8_0, emb8_1, emb8_2,
    emb8_3, emb8_4, emb8_5, emb8_6, emb8_7] using hh

end QCert.LiRossSelinger
