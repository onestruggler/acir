/-
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

/-- The word `V` of `K ≈ V K S` (evenly many signs). -/
def V325e : Bool → Bool → Bool → Bool → List (Gen 4)
  | false, false, false, false => []
  | false, false, true, true => [Gen.x 0 2 (by decide), Gen.x 1 3 (by decide)]
  | false, true, false, true => [Gen.x 0 1 (by decide), Gen.x 2 3 (by decide)]
  | false, true, true, false => [Gen.x 0 3 (by decide), Gen.x 1 2 (by decide)]
  | true, false, false, true => [Gen.x 0 3 (by decide), Gen.x 1 2 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 2, Gen.neg 3]
  | true, false, true, false => [Gen.x 0 1 (by decide), Gen.x 2 3 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 2, Gen.neg 3]
  | true, true, false, false => [Gen.x 0 2 (by decide), Gen.x 1 3 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 2, Gen.neg 3]
  | true, true, true, true => [Gen.neg 0, Gen.neg 1, Gen.neg 2, Gen.neg 3]
  | _, _, _, _ => []

/-- The chains of `K ≈ V K S`. -/
def S325e : Bool → Bool → Bool → Bool → List (GStep ((Fam ⊕ MFam) × Bool) 4)
  | false, false, false, false =>
    []
  | false, false, true, true =>
    [⟨(.inl .r1a, false), [0, 2], false, 0⟩, ⟨(.inl .r1a, false), [1, 3], false, 1⟩, ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 3⟩, ⟨(.inr .ksym6, false), [0, 1, 2, 3], true, 2⟩,
      ⟨(.inl .r1a, false), [2, 3], true, 3⟩]
  | false, true, false, true =>
    [⟨(.inl .r1a, false), [0, 1], false, 0⟩, ⟨(.inl .r1a, false), [2, 3], false, 1⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 3⟩, ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 2⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 3⟩]
  | false, true, true, false =>
    [⟨(.inl .r1a, false), [0, 3], false, 0⟩, ⟨(.inl .r1a, false), [1, 2], false, 1⟩, ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 3⟩, ⟨(.inr .ksym2, false), [0, 1, 2, 3], true, 2⟩,
      ⟨(.inl .r3a, false), [1, 2, 3], true, 3⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 3⟩, ⟨(.inl .r1a, false), [2, 3], true, 4⟩, ⟨(.inl .r1a, false), [1, 3], true, 3⟩]
  | true, false, false, true =>
    [⟨(.inl .r1b, false), [1], false, 0⟩, ⟨(.inl .r1b, false), [0], false, 0⟩, ⟨(.inl .r2d, false), [0, 1], true, 1⟩, ⟨(.inl .r1a, false), [0, 3], false, 2⟩,
      ⟨(.inl .r2d, false), [0, 1], true, 0⟩, ⟨(.inl .r3c, false), [0, 3], false, 1⟩, ⟨(.inl .r2b, false), [0, 3, 1], false, 0⟩, ⟨(.inl .r1b, false), [2], false, 2⟩,
      ⟨(.inl .r2d, false), [2, 3], true, 3⟩, ⟨(.inl .r1b, false), [0], false, 4⟩, ⟨(.inl .r2d, false), [0, 3], false, 3⟩, ⟨(.inl .r2d, false), [0, 2], false, 2⟩,
      ⟨(.inl .r2d, false), [0, 1], false, 1⟩, ⟨(.inl .r1a, false), [1, 2], false, 4⟩, ⟨(.inl .r2b, false), [1, 2, 3], true, 5⟩, ⟨(.inl .r2d, false), [1, 2], true, 2⟩,
      ⟨(.inl .r3c, false), [1, 2], false, 3⟩, ⟨(.inl .r3c, true), [1, 2], true, 2⟩, ⟨(.inl .r2b, false), [1, 2, 0], false, 1⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 10⟩,
      ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 9⟩, ⟨(.inr .k22, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .ksym2, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inl .r3b, false), [0, 1, 2], true, 7⟩,
      ⟨(.inl .r3b, true), [1, 2, 3], true, 8⟩, ⟨(.inl .r2b, false), [1, 3, 0], true, 9⟩, ⟨(.inl .r3c, true), [1, 3], false, 10⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 11⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 10⟩, ⟨(.inl .r3c, false), [1, 3], true, 12⟩, ⟨(.inl .r1a, false), [1, 3], true, 13⟩, ⟨(.inl .r2d, false), [1, 3], false, 11⟩,
      ⟨(.inl .r2d, false), [1, 2], false, 10⟩, ⟨(.inl .r2b, false), [2, 3, 0], true, 8⟩, ⟨(.inl .r2b, false), [2, 3, 1], true, 9⟩, ⟨(.inl .r3c, true), [2, 3], false, 10⟩,
      ⟨(.inl .r3c, false), [2, 3], true, 11⟩, ⟨(.inl .r1a, false), [2, 3], true, 12⟩, ⟨(.inl .r2d, false), [2, 3], false, 10⟩, ⟨(.inl .r2d, false), [1, 2], true, 9⟩,
      ⟨(.inl .r2d, false), [1, 3], true, 10⟩, ⟨(.inl .r2d, false), [2, 3], true, 9⟩, ⟨(.inl .r3c, false), [1, 3], false, 11⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 10⟩,
      ⟨(.inl .r3c, true), [1, 3], true, 9⟩, ⟨(.inl .r2b, false), [1, 3, 0], false, 8⟩, ⟨(.inl .r2d, false), [1, 2], true, 10⟩, ⟨(.inl .r2d, false), [1, 3], true, 11⟩,
      ⟨(.inl .r1b, false), [1], true, 12⟩, ⟨(.inl .r2d, false), [2, 3], false, 11⟩, ⟨(.inl .r1b, false), [2], true, 10⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], true, 7⟩,
      ⟨(.inl .r3c, true), [0, 2], false, 8⟩, ⟨(.inl .r2b, false), [0, 2, 3], true, 9⟩, ⟨(.inl .r1a, false), [0, 2], true, 10⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 7⟩,
      ⟨(.inl .r3c, false), [1, 3], true, 8⟩, ⟨(.inl .r2d, false), [1, 2], false, 7⟩, ⟨(.inl .r1a, false), [1, 3], true, 9⟩, ⟨(.inl .r2d, false), [0, 2], false, 8⟩,
      ⟨(.inl .r2d, false), [0, 1], false, 7⟩, ⟨(.inl .r2d, false), [1, 2], false, 9⟩, ⟨(.inl .r1b, false), [1], true, 8⟩, ⟨(.inl .r1b, false), [2], true, 8⟩]
  | true, false, true, false =>
    [⟨(.inl .r1a, false), [0, 1], false, 0⟩, ⟨(.inl .r1b, false), [1], false, 1⟩, ⟨(.inl .r1b, false), [0], false, 1⟩, ⟨(.inl .r2d, false), [0, 1], true, 2⟩,
      ⟨(.inl .r1a, false), [2, 3], false, 3⟩, ⟨(.inl .r2b, false), [2, 3, 1], false, 2⟩, ⟨(.inl .r2b, false), [2, 3, 0], false, 1⟩, ⟨(.inl .r1b, false), [3], false, 4⟩,
      ⟨(.inl .r1b, false), [2], false, 4⟩, ⟨(.inl .r2d, false), [2, 3], true, 5⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 11⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 9⟩,
      ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 8⟩, ⟨(.inr .k11, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inl .r1a, false), [1, 3], true, 8⟩, ⟨(.inl .r1a, false), [0, 2], true, 7⟩,
      ⟨(.inl .r2b, false), [1, 3, 0], true, 7⟩, ⟨(.inl .r3c, true), [1, 3], false, 8⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 9⟩, ⟨(.inl .r2d, false), [2, 3], false, 8⟩,
      ⟨(.inl .r3c, false), [1, 3], true, 10⟩, ⟨(.inl .r2d, false), [1, 3], false, 9⟩, ⟨(.inl .r1a, false), [1, 3], true, 11⟩, ⟨(.inl .r2d, false), [1, 2], false, 8⟩,
      ⟨(.inl .r2d, false), [1, 2], true, 8⟩, ⟨(.inl .r2d, false), [1, 3], true, 9⟩, ⟨(.inl .r1b, false), [1], true, 10⟩, ⟨(.inl .r1b, false), [3], true, 9⟩]
  | true, true, false, false =>
    [⟨(.inl .r1b, false), [1], false, 0⟩, ⟨(.inl .r1b, false), [0], false, 0⟩, ⟨(.inl .r2d, false), [0, 1], true, 1⟩, ⟨(.inl .r1a, false), [0, 2], false, 2⟩,
      ⟨(.inl .r2d, false), [0, 1], true, 0⟩, ⟨(.inl .r3c, false), [0, 2], false, 1⟩, ⟨(.inl .r2b, false), [0, 2, 1], false, 0⟩, ⟨(.inl .r1b, false), [3], false, 3⟩,
      ⟨(.inl .r1b, false), [0], false, 4⟩, ⟨(.inl .r2d, false), [0, 3], false, 3⟩, ⟨(.inl .r2d, false), [0, 2], false, 2⟩, ⟨(.inl .r2d, false), [0, 1], false, 1⟩,
      ⟨(.inl .r2d, false), [1, 2], true, 2⟩, ⟨(.inl .r2d, false), [1, 3], true, 3⟩, ⟨(.inl .r2d, false), [2, 3], true, 2⟩, ⟨(.inl .r1a, false), [1, 3], false, 5⟩,
      ⟨(.inl .r3c, false), [1, 3], false, 4⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 3⟩, ⟨(.inl .r3c, true), [1, 3], true, 2⟩, ⟨(.inl .r2b, false), [1, 3, 0], false, 1⟩,
      ⟨(.inr .k12, false), [0, 1, 2, 3], true, 10⟩, ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 9⟩, ⟨(.inr .k32, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .ksym6, false), [0, 1, 2, 3], true, 6⟩,
      ⟨(.inl .r3b, true), [0, 2, 3], false, 7⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 8⟩, ⟨(.inl .r2b, false), [2, 3, 0], true, 9⟩, ⟨(.inl .r2b, false), [2, 3, 1], true, 10⟩,
      ⟨(.inl .r3c, true), [2, 3], false, 11⟩, ⟨(.inl .r3c, false), [2, 3], true, 12⟩, ⟨(.inl .r1a, false), [2, 3], true, 13⟩, ⟨(.inl .r2d, false), [2, 3], false, 11⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 12⟩, ⟨(.inl .r1b, false), [2], true, 11⟩, ⟨(.inl .r1b, false), [3], true, 11⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], true, 7⟩,
      ⟨(.inl .r3c, true), [0, 2], false, 8⟩, ⟨(.inl .r2b, false), [0, 2, 1], true, 9⟩, ⟨(.inl .r2d, false), [1, 2], false, 8⟩, ⟨(.inl .r1a, false), [0, 2], true, 10⟩,
      ⟨(.inl .r3c, true), [1, 3], false, 7⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 8⟩, ⟨(.inl .r2d, false), [2, 3], false, 7⟩, ⟨(.inl .r1a, false), [1, 3], true, 9⟩,
      ⟨(.inl .r2d, false), [0, 3], false, 8⟩, ⟨(.inl .r2d, false), [0, 2], false, 7⟩, ⟨(.inl .r2d, false), [1, 3], false, 9⟩, ⟨(.inl .r2d, false), [1, 2], false, 8⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 10⟩, ⟨(.inl .r1b, false), [2], true, 9⟩, ⟨(.inl .r1b, false), [3], true, 9⟩]
  | true, true, true, true =>
    [⟨(.inl .r1b, false), [1], false, 0⟩, ⟨(.inl .r1b, false), [0], false, 0⟩, ⟨(.inl .r2d, false), [0, 1], true, 1⟩, ⟨(.inl .r1b, false), [3], false, 2⟩,
      ⟨(.inl .r1b, false), [2], false, 2⟩, ⟨(.inl .r2d, false), [2, 3], true, 3⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inr .k11, false), [0, 1, 2, 3], true, 4⟩,
      ⟨(.inl .r2a, false), [0, 2, 1, 3], false, 6⟩, ⟨(.inl .r1a, false), [0, 2], true, 5⟩, ⟨(.inl .r1a, false), [1, 3], true, 5⟩]
  | _, _, _, _ => []

/-- The word `V` of `K S' K ≈ V K S` (oddly many signs at both). -/
def V325o : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool → List (Gen 4)
  | false, false, false, true, false, false, false, true => [Gen.x 1 2 (by decide), Gen.neg 3]
  | false, false, false, true, false, false, true, false => [Gen.x 0 2 (by decide), Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.neg 3]
  | false, false, false, true, false, true, false, false => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 2 3 (by decide), Gen.neg 3]
  | false, false, false, true, false, true, true, true => [Gen.x 0 3 (by decide), Gen.neg 3]
  | false, false, false, true, true, false, false, false => [Gen.x 0 3 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 2]
  | false, false, false, true, true, false, true, true => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 2 3 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 2]
  | false, false, false, true, true, true, false, true => [Gen.x 0 2 (by decide), Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 2]
  | false, false, false, true, true, true, true, false => [Gen.x 1 2 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 2]
  | false, false, true, false, false, false, false, true => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 2 3 (by decide), Gen.neg 1]
  | false, false, true, false, false, false, true, false => [Gen.x 0 3 (by decide), Gen.neg 1]
  | false, false, true, false, false, true, false, false => [Gen.x 1 2 (by decide), Gen.neg 1]
  | false, false, true, false, false, true, true, true => [Gen.x 0 2 (by decide), Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.neg 1]
  | false, false, true, false, true, false, false, false => [Gen.x 0 2 (by decide), Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.neg 0, Gen.neg 2, Gen.neg 3]
  | false, false, true, false, true, false, true, true => [Gen.x 1 2 (by decide), Gen.neg 0, Gen.neg 2, Gen.neg 3]
  | false, false, true, false, true, true, false, true => [Gen.x 0 3 (by decide), Gen.neg 0, Gen.neg 2, Gen.neg 3]
  | false, false, true, false, true, true, true, false => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 2 3 (by decide), Gen.neg 0, Gen.neg 2, Gen.neg 3]
  | false, true, false, false, false, false, false, true => [Gen.x 0 2 (by decide), Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.neg 2]
  | false, true, false, false, false, false, true, false => [Gen.x 1 2 (by decide), Gen.neg 2]
  | false, true, false, false, false, true, false, false => [Gen.x 0 3 (by decide), Gen.neg 2]
  | false, true, false, false, false, true, true, true => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 2 3 (by decide), Gen.neg 2]
  | false, true, false, false, true, false, false, false => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 2 3 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 3]
  | false, true, false, false, true, false, true, true => [Gen.x 0 3 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 3]
  | false, true, false, false, true, true, false, true => [Gen.x 1 2 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 3]
  | false, true, false, false, true, true, true, false => [Gen.x 0 2 (by decide), Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 3]
  | false, true, true, true, false, false, false, true => [Gen.x 0 3 (by decide), Gen.neg 0]
  | false, true, true, true, false, false, true, false => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 2 3 (by decide), Gen.neg 0]
  | false, true, true, true, false, true, false, false => [Gen.x 0 2 (by decide), Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.neg 0]
  | false, true, true, true, false, true, true, true => [Gen.x 1 2 (by decide), Gen.neg 0]
  | false, true, true, true, true, false, false, false => [Gen.x 1 2 (by decide), Gen.neg 1, Gen.neg 2, Gen.neg 3]
  | false, true, true, true, true, false, true, true => [Gen.x 0 2 (by decide), Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.neg 1, Gen.neg 2, Gen.neg 3]
  | false, true, true, true, true, true, false, true => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 2 3 (by decide), Gen.neg 1, Gen.neg 2, Gen.neg 3]
  | false, true, true, true, true, true, true, false => [Gen.x 0 3 (by decide), Gen.neg 1, Gen.neg 2, Gen.neg 3]
  | true, false, false, false, false, false, false, true => [Gen.x 0 3 (by decide), Gen.neg 1, Gen.neg 2, Gen.neg 3]
  | true, false, false, false, false, false, true, false => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 2 3 (by decide), Gen.neg 1, Gen.neg 2, Gen.neg 3]
  | true, false, false, false, false, true, false, false => [Gen.x 0 2 (by decide), Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.neg 1, Gen.neg 2, Gen.neg 3]
  | true, false, false, false, false, true, true, true => [Gen.x 1 2 (by decide), Gen.neg 1, Gen.neg 2, Gen.neg 3]
  | true, false, false, false, true, false, false, false => [Gen.x 1 2 (by decide), Gen.neg 0]
  | true, false, false, false, true, false, true, true => [Gen.x 0 2 (by decide), Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.neg 0]
  | true, false, false, false, true, true, false, true => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 2 3 (by decide), Gen.neg 0]
  | true, false, false, false, true, true, true, false => [Gen.x 0 3 (by decide), Gen.neg 0]
  | true, false, true, true, false, false, false, true => [Gen.x 0 2 (by decide), Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 3]
  | true, false, true, true, false, false, true, false => [Gen.x 1 2 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 3]
  | true, false, true, true, false, true, false, false => [Gen.x 0 3 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 3]
  | true, false, true, true, false, true, true, true => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 2 3 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 3]
  | true, false, true, true, true, false, false, false => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 2 3 (by decide), Gen.neg 2]
  | true, false, true, true, true, false, true, true => [Gen.x 0 3 (by decide), Gen.neg 2]
  | true, false, true, true, true, true, false, true => [Gen.x 1 2 (by decide), Gen.neg 2]
  | true, false, true, true, true, true, true, false => [Gen.x 0 2 (by decide), Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.neg 2]
  | true, true, false, true, false, false, false, true => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 2 3 (by decide), Gen.neg 0, Gen.neg 2, Gen.neg 3]
  | true, true, false, true, false, false, true, false => [Gen.x 0 3 (by decide), Gen.neg 0, Gen.neg 2, Gen.neg 3]
  | true, true, false, true, false, true, false, false => [Gen.x 1 2 (by decide), Gen.neg 0, Gen.neg 2, Gen.neg 3]
  | true, true, false, true, false, true, true, true => [Gen.x 0 2 (by decide), Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.neg 0, Gen.neg 2, Gen.neg 3]
  | true, true, false, true, true, false, false, false => [Gen.x 0 2 (by decide), Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.neg 1]
  | true, true, false, true, true, false, true, true => [Gen.x 1 2 (by decide), Gen.neg 1]
  | true, true, false, true, true, true, false, true => [Gen.x 0 3 (by decide), Gen.neg 1]
  | true, true, false, true, true, true, true, false => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 2 3 (by decide), Gen.neg 1]
  | true, true, true, false, false, false, false, true => [Gen.x 1 2 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 2]
  | true, true, true, false, false, false, true, false => [Gen.x 0 2 (by decide), Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 2]
  | true, true, true, false, false, true, false, false => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 2 3 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 2]
  | true, true, true, false, false, true, true, true => [Gen.x 0 3 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 2]
  | true, true, true, false, true, false, false, false => [Gen.x 0 3 (by decide), Gen.neg 3]
  | true, true, true, false, true, false, true, true => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 2 3 (by decide), Gen.neg 3]
  | true, true, true, false, true, true, false, true => [Gen.x 0 2 (by decide), Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.neg 3]
  | true, true, true, false, true, true, true, false => [Gen.x 1 2 (by decide), Gen.neg 3]
  | _, _, _, _, _, _, _, _ => []

/-- The chains of `K S' K ≈ V K S`. -/
def S325o : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool →
    List (GStep ((Fam ⊕ MFam) × Bool) 4)
  | false, false, false, true, false, false, false, true =>
    [⟨(.inl .r1b, false), [0], false, 1⟩, ⟨(.inr .k32, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1b, false), [3], false, 2⟩,
      ⟨(.inl .r2d, false), [0, 3], true, 1⟩, ⟨(.inr .k32, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inl .r2d, false), [0, 1], true, 5⟩, ⟨(.inl .r2d, false), [0, 2], true, 6⟩,
      ⟨(.inl .r2d, false), [0, 3], true, 7⟩, ⟨(.inl .r1b, false), [0], true, 8⟩, ⟨(.inl .r2a, false), [0, 3, 1, 2], true, 3⟩, ⟨(.inl .r2b, false), [0, 3, 1], true, 4⟩,
      ⟨(.inl .r2b, false), [0, 3, 2], true, 5⟩, ⟨(.inl .r3c, false), [0, 3], true, 6⟩, ⟨(.inl .r2d, false), [0, 2], false, 5⟩, ⟨(.inl .r1a, false), [0, 3], true, 7⟩,
      ⟨(.inl .r2d, false), [0, 1], false, 4⟩, ⟨(.inl .r2b, false), [1, 2, 0], true, 3⟩, ⟨(.inl .r3c, true), [1, 2], false, 4⟩, ⟨(.inl .r3c, false), [1, 2], true, 5⟩,
      ⟨(.inl .r2d, false), [1, 2], false, 4⟩, ⟨(.inl .r1a, false), [1, 2], true, 6⟩, ⟨(.inl .r2d, false), [0, 1], true, 3⟩, ⟨(.inl .r2d, false), [0, 2], true, 4⟩,
      ⟨(.inl .r1b, false), [0], true, 5⟩, ⟨(.inl .r2d, false), [1, 2], false, 4⟩, ⟨(.inl .r1b, false), [1], true, 3⟩, ⟨(.inl .r1b, false), [2], true, 3⟩]
  | false, false, false, true, false, false, true, false =>
    [⟨(.inl .r1b, false), [0], false, 1⟩, ⟨(.inr .k22, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 2⟩,
      ⟨(.inl .r3c, false), [0, 1], false, 1⟩, ⟨(.inl .r3b, false), [0, 1, 2], true, 0⟩, ⟨(.inl .r1b, false), [2], false, 3⟩, ⟨(.inl .r2d, false), [1, 2], true, 2⟩,
      ⟨(.inl .r1a, false), [2, 3], false, 2⟩, ⟨(.inl .r3c, true), [2, 3], false, 3⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .k31, false), [0, 1, 2, 3], true, 5⟩,
      ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r3b, true), [0, 1, 3], false, 5⟩, ⟨(.inl .r3a, true), [1, 2, 3], true, 6⟩, ⟨(.inl .r3b, true), [1, 2, 3], false, 7⟩,
      ⟨(.inl .r1a, false), [1, 2], true, 6⟩, ⟨(.inl .r2d, false), [0, 3], false, 8⟩, ⟨(.inl .r2d, false), [0, 1], false, 7⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 5⟩,
      ⟨(.inl .r3c, true), [0, 1], false, 6⟩, ⟨(.inl .r3c, false), [0, 1], true, 7⟩, ⟨(.inl .r2d, false), [0, 1], false, 6⟩, ⟨(.inl .r2b, false), [0, 1, 3], false, 9⟩,
      ⟨(.inl .r1a, false), [0, 1], true, 8⟩, ⟨(.inl .r2b, false), [2, 3, 0], true, 5⟩, ⟨(.inl .r2b, false), [2, 3, 1], true, 6⟩, ⟨(.inl .r3c, false), [2, 3], true, 7⟩,
      ⟨(.inl .r1a, false), [2, 3], true, 8⟩, ⟨(.inl .r2d, false), [0, 1], true, 5⟩, ⟨(.inl .r2d, false), [0, 2], true, 6⟩, ⟨(.inl .r1b, false), [0], true, 7⟩,
      ⟨(.inl .r2d, false), [1, 2], false, 6⟩, ⟨(.inl .r1b, false), [1], true, 5⟩, ⟨(.inl .r1b, false), [2], true, 5⟩]
  | false, false, false, true, false, true, false, false =>
    [⟨(.inl .r1b, false), [0], false, 1⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1b, false), [1], false, 2⟩,
      ⟨(.inl .r2d, false), [0, 1], true, 1⟩, ⟨(.inl .r1a, false), [0, 2], false, 2⟩, ⟨(.inl .r2b, false), [0, 2, 1], false, 1⟩, ⟨(.inl .r3b, true), [0, 1, 2], false, 0⟩,
      ⟨(.inl .r1a, false), [1, 3], false, 3⟩, ⟨(.inl .r3c, false), [1, 3], false, 2⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 1⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 1⟩,
      ⟨(.inr .k12, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inr .ksym6, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r1a, false), [2, 3], true, 5⟩,
      ⟨(.inl .r2b, false), [0, 2, 3], false, 6⟩, ⟨(.inl .r3c, true), [0, 2], true, 5⟩, ⟨(.inl .r3c, true), [1, 3], true, 7⟩, ⟨(.inl .r2b, false), [1, 3, 0], false, 6⟩,
      ⟨(.inl .r2d, false), [0, 1], false, 8⟩, ⟨(.inl .r1b, false), [0], true, 7⟩, ⟨(.inl .r1b, false), [1], true, 7⟩, ⟨(.inl .r2d, false), [0, 3], false, 8⟩,
      ⟨(.inl .r2d, false), [0, 2], false, 7⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], true, 5⟩, ⟨(.inl .r3c, true), [0, 2], false, 6⟩, ⟨(.inl .r3c, false), [0, 2], true, 7⟩,
      ⟨(.inl .r2d, false), [0, 2], false, 6⟩, ⟨(.inl .r2b, false), [0, 2, 3], false, 9⟩, ⟨(.inl .r1a, false), [0, 2], true, 8⟩, ⟨(.inl .r2b, false), [1, 3, 0], true, 5⟩,
      ⟨(.inl .r2b, false), [1, 3, 2], true, 6⟩, ⟨(.inl .r3c, false), [1, 3], true, 7⟩, ⟨(.inl .r2d, false), [1, 2], false, 6⟩, ⟨(.inl .r1a, false), [1, 3], true, 8⟩,
      ⟨(.inl .r2d, false), [0, 1], true, 5⟩, ⟨(.inl .r2d, false), [0, 2], true, 6⟩, ⟨(.inl .r1b, false), [0], true, 7⟩, ⟨(.inl .r2d, false), [1, 2], false, 6⟩,
      ⟨(.inl .r1b, false), [1], true, 5⟩, ⟨(.inl .r1b, false), [2], true, 5⟩]
  | false, false, false, true, false, true, true, true =>
    [⟨(.inl .r1b, false), [0], false, 1⟩, ⟨(.inl .r2d, false), [1, 2], true, 3⟩, ⟨(.inl .r2d, false), [1, 3], true, 4⟩, ⟨(.inl .r2d, false), [0, 2], true, 2⟩,
      ⟨(.inl .r2d, false), [0, 3], true, 3⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inr .k11, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], false, 4⟩,
      ⟨(.inl .r1a, false), [0, 2], true, 3⟩, ⟨(.inl .r1a, false), [1, 3], true, 3⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 3], false, 2⟩,
      ⟨(.inl .r3c, false), [0, 3], false, 1⟩, ⟨(.inl .r2a, false), [0, 3, 1, 2], false, 0⟩, ⟨(.inl .r2b, false), [1, 2, 3], true, 1⟩, ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 3⟩,
      ⟨(.inr .ksym2, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 3⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 3⟩, ⟨(.inl .r1a, false), [2, 3], true, 4⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 3⟩, ⟨(.inl .r2d, false), [0, 2], false, 4⟩, ⟨(.inl .r2d, false), [0, 1], false, 3⟩, ⟨(.inl .r2d, false), [0, 1], true, 3⟩,
      ⟨(.inl .r2d, false), [0, 2], true, 4⟩, ⟨(.inl .r1b, false), [0], true, 5⟩, ⟨(.inl .r2d, false), [1, 2], false, 4⟩, ⟨(.inl .r1b, false), [1], true, 3⟩,
      ⟨(.inl .r1b, false), [2], true, 3⟩]
  | false, false, false, true, true, false, false, false =>
    [⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1b, false), [1], false, 2⟩, ⟨(.inl .r2d, false), [0, 1], true, 1⟩, ⟨(.inl .r1a, false), [0, 3], false, 2⟩,
      ⟨(.inl .r2b, false), [0, 3, 1], false, 1⟩, ⟨(.inl .r2a, false), [0, 3, 1, 2], false, 0⟩, ⟨(.inl .r1b, false), [2], false, 3⟩, ⟨(.inl .r1b, false), [0], false, 4⟩,
      ⟨(.inl .r2d, false), [0, 2], false, 3⟩, ⟨(.inl .r2d, false), [0, 1], false, 2⟩, ⟨(.inl .r2b, false), [1, 2, 0], true, 1⟩, ⟨(.inl .r3c, true), [1, 2], false, 2⟩,
      ⟨(.inl .r3c, false), [1, 2], true, 3⟩, ⟨(.inl .r2d, false), [1, 2], false, 2⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 8⟩, ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 7⟩,
      ⟨(.inr .k22, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inr .ksym2, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r3b, false), [0, 1, 2], true, 5⟩, ⟨(.inl .r3b, true), [1, 2, 3], true, 6⟩,
      ⟨(.inl .r2b, false), [1, 3, 0], true, 7⟩, ⟨(.inl .r3c, true), [1, 3], false, 8⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 9⟩, ⟨(.inl .r2d, false), [2, 3], false, 8⟩,
      ⟨(.inl .r3c, false), [1, 3], true, 10⟩, ⟨(.inl .r1a, false), [1, 3], true, 11⟩, ⟨(.inl .r2d, false), [1, 3], false, 9⟩, ⟨(.inl .r2d, false), [1, 2], false, 8⟩,
      ⟨(.inl .r2b, false), [2, 3, 0], true, 6⟩, ⟨(.inl .r2b, false), [2, 3, 1], true, 7⟩, ⟨(.inl .r3c, true), [2, 3], false, 8⟩, ⟨(.inl .r3c, false), [2, 3], true, 9⟩,
      ⟨(.inl .r1a, false), [2, 3], true, 10⟩, ⟨(.inl .r2d, false), [2, 3], false, 8⟩, ⟨(.inl .r2d, false), [1, 2], true, 7⟩, ⟨(.inl .r2d, false), [1, 3], true, 8⟩,
      ⟨(.inl .r2d, false), [2, 3], true, 7⟩, ⟨(.inl .r3c, false), [1, 3], false, 9⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 8⟩, ⟨(.inl .r3c, true), [1, 3], true, 7⟩,
      ⟨(.inl .r2b, false), [1, 3, 0], false, 6⟩, ⟨(.inl .r2d, false), [1, 2], true, 8⟩, ⟨(.inl .r2d, false), [1, 3], true, 9⟩, ⟨(.inl .r1b, false), [1], true, 10⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 9⟩, ⟨(.inl .r1b, false), [2], true, 8⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], true, 5⟩, ⟨(.inl .r3c, true), [0, 2], false, 6⟩,
      ⟨(.inl .r2b, false), [0, 2, 3], true, 7⟩, ⟨(.inl .r1a, false), [0, 2], true, 8⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 5⟩, ⟨(.inl .r3c, false), [1, 3], true, 6⟩,
      ⟨(.inl .r2d, false), [1, 2], false, 5⟩, ⟨(.inl .r1a, false), [1, 3], true, 7⟩, ⟨(.inl .r2d, false), [0, 2], false, 6⟩, ⟨(.inl .r2d, false), [0, 1], false, 5⟩,
      ⟨(.inl .r2d, false), [1, 2], false, 7⟩, ⟨(.inl .r1b, false), [1], true, 6⟩, ⟨(.inl .r1b, false), [2], true, 6⟩, ⟨(.inl .r2d, false), [0, 3], false, 6⟩,
      ⟨(.inl .r1b, false), [0], true, 5⟩]
  | false, false, false, true, true, false, true, true =>
    [⟨(.inr .k11, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 2], false, 2⟩, ⟨(.inl .r3c, false), [0, 2], false, 1⟩,
      ⟨(.inl .r3b, true), [0, 1, 2], false, 0⟩, ⟨(.inl .r1b, false), [3], false, 3⟩, ⟨(.inl .r1b, false), [0], false, 4⟩, ⟨(.inl .r2d, false), [0, 3], false, 3⟩,
      ⟨(.inl .r2d, false), [0, 2], false, 2⟩, ⟨(.inl .r2d, false), [2, 3], true, 3⟩, ⟨(.inl .r1a, false), [1, 3], false, 5⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 4⟩,
      ⟨(.inl .r3c, true), [1, 3], true, 3⟩, ⟨(.inl .r2b, false), [1, 3, 0], false, 2⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 1⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 1⟩,
      ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 9⟩, ⟨(.inr .k32, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .ksym6, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inl .r3b, true), [0, 2, 3], false, 7⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], true, 8⟩, ⟨(.inl .r2b, false), [2, 3, 0], true, 9⟩, ⟨(.inl .r2b, false), [2, 3, 1], true, 10⟩, ⟨(.inl .r3c, true), [2, 3], false, 11⟩,
      ⟨(.inl .r3c, false), [2, 3], true, 12⟩, ⟨(.inl .r1a, false), [2, 3], true, 13⟩, ⟨(.inl .r2d, false), [2, 3], false, 11⟩, ⟨(.inl .r2d, false), [2, 3], false, 12⟩,
      ⟨(.inl .r1b, false), [2], true, 11⟩, ⟨(.inl .r1b, false), [3], true, 11⟩, ⟨(.inl .r2d, false), [0, 1], false, 10⟩, ⟨(.inl .r1b, false), [0], true, 9⟩,
      ⟨(.inl .r2a, false), [0, 2, 1, 3], true, 7⟩, ⟨(.inl .r2b, false), [0, 2, 1], true, 8⟩, ⟨(.inl .r1a, false), [0, 2], true, 9⟩, ⟨(.inl .r3c, false), [1, 3], false, 8⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 7⟩]
  | false, false, false, true, true, true, false, true =>
    [⟨(.inr .k21, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 2⟩, ⟨(.inl .r3c, false), [0, 1], false, 1⟩,
      ⟨(.inl .r3b, false), [0, 1, 2], true, 0⟩, ⟨(.inl .r1b, false), [3], false, 3⟩, ⟨(.inl .r1b, false), [0], false, 4⟩, ⟨(.inl .r2d, false), [0, 3], false, 3⟩,
      ⟨(.inl .r2d, false), [0, 1], false, 2⟩, ⟨(.inl .r1a, false), [2, 3], false, 5⟩, ⟨(.inl .r3c, true), [2, 3], true, 4⟩, ⟨(.inl .r2b, false), [2, 3, 1], false, 3⟩,
      ⟨(.inl .r2b, false), [2, 3, 0], false, 2⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 9⟩, ⟨(.inr .k32, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 6⟩,
      ⟨(.inl .r3b, true), [0, 1, 3], false, 7⟩, ⟨(.inl .r3a, true), [1, 2, 3], true, 8⟩, ⟨(.inl .r3b, true), [1, 2, 3], true, 8⟩, ⟨(.inl .r2b, false), [1, 3, 0], true, 9⟩,
      ⟨(.inl .r3c, true), [1, 3], false, 10⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 11⟩, ⟨(.inl .r2d, false), [2, 3], false, 10⟩, ⟨(.inl .r3c, false), [1, 3], true, 12⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 13⟩, ⟨(.inl .r2d, false), [1, 3], false, 11⟩, ⟨(.inl .r2d, false), [1, 2], false, 10⟩, ⟨(.inl .r2d, false), [1, 2], true, 10⟩,
      ⟨(.inl .r2d, false), [1, 3], true, 11⟩, ⟨(.inl .r1b, false), [1], true, 12⟩, ⟨(.inl .r1b, false), [3], true, 11⟩, ⟨(.inl .r2d, false), [0, 2], false, 10⟩,
      ⟨(.inl .r1b, false), [0], true, 9⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inl .r2b, false), [0, 1, 2], true, 8⟩, ⟨(.inl .r1a, false), [0, 1], true, 9⟩,
      ⟨(.inl .r3c, false), [2, 3], false, 8⟩, ⟨(.inl .r1a, false), [2, 3], true, 7⟩]
  | false, false, false, true, true, true, true, false =>
    [⟨(.inr .k31, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1b, false), [2], false, 2⟩, ⟨(.inl .r1b, false), [1], false, 2⟩,
      ⟨(.inl .r2d, false), [1, 2], true, 3⟩, ⟨(.inr .k31, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r2a, false), [0, 3, 1, 2], true, 5⟩, ⟨(.inl .r3c, true), [0, 3], false, 6⟩,
      ⟨(.inl .r1a, false), [0, 3], true, 7⟩, ⟨(.inl .r2b, false), [1, 2, 3], false, 6⟩, ⟨(.inl .r1a, false), [1, 2], true, 5⟩]
  | false, false, true, false, false, false, false, true =>
    [⟨(.inl .r1b, false), [0], false, 1⟩, ⟨(.inr .k32, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 2], false, 2⟩,
      ⟨(.inl .r3c, false), [0, 2], false, 1⟩, ⟨(.inl .r3b, true), [0, 1, 2], false, 0⟩, ⟨(.inl .r1a, false), [1, 3], false, 3⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 2⟩,
      ⟨(.inl .r3a, false), [1, 2, 3], true, 1⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 1⟩, ⟨(.inl .r1b, false), [1], false, 3⟩, ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 7⟩,
      ⟨(.inr .ksym6, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inr .k31, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r1a, false), [2, 3], true, 7⟩, ⟨(.inl .r2d, false), [0, 3], false, 8⟩,
      ⟨(.inl .r2d, false), [0, 2], false, 7⟩, ⟨(.inl .r2a, false), [0, 3, 1, 2], true, 5⟩, ⟨(.inl .r3c, true), [0, 3], false, 6⟩, ⟨(.inl .r2b, false), [0, 3, 2], true, 7⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 6⟩, ⟨(.inl .r3c, false), [0, 3], true, 8⟩, ⟨(.inl .r2d, false), [0, 3], false, 7⟩, ⟨(.inl .r1a, false), [0, 3], true, 9⟩,
      ⟨(.inl .r2d, false), [0, 2], false, 6⟩, ⟨(.inl .r2b, false), [1, 2, 0], true, 5⟩, ⟨(.inl .r3c, false), [1, 2], true, 6⟩, ⟨(.inl .r2b, false), [1, 2, 3], true, 7⟩,
      ⟨(.inl .r1a, false), [1, 2], true, 8⟩, ⟨(.inl .r2d, false), [0, 1], true, 5⟩, ⟨(.inl .r2d, false), [0, 3], true, 6⟩, ⟨(.inl .r1b, false), [0], true, 7⟩,
      ⟨(.inl .r2d, false), [1, 3], false, 6⟩, ⟨(.inl .r1b, false), [1], true, 5⟩, ⟨(.inl .r2d, false), [2, 3], false, 5⟩, ⟨(.inl .r1b, false), [3], true, 6⟩]
  | false, false, true, false, false, false, true, false =>
    [⟨(.inl .r1b, false), [0], false, 1⟩, ⟨(.inr .k22, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1b, false), [2], false, 2⟩,
      ⟨(.inl .r2d, false), [0, 2], true, 1⟩, ⟨(.inl .r1a, false), [0, 3], false, 2⟩, ⟨(.inl .r2b, false), [0, 3, 2], false, 1⟩, ⟨(.inl .r2a, false), [0, 3, 1, 2], false, 0⟩,
      ⟨(.inl .r3c, false), [1, 2], true, 1⟩, ⟨(.inr .k22, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 3⟩, ⟨(.inr .ksym2, false), [0, 1, 2, 3], true, 2⟩,
      ⟨(.inl .r3a, false), [1, 2, 3], true, 3⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 3⟩, ⟨(.inl .r1a, false), [2, 3], true, 4⟩, ⟨(.inl .r1a, false), [1, 3], true, 3⟩,
      ⟨(.inl .r2b, false), [0, 1, 2], false, 4⟩, ⟨(.inl .r3c, true), [0, 1], true, 3⟩, ⟨(.inl .r3c, false), [2, 3], false, 5⟩, ⟨(.inl .r2b, false), [2, 3, 0], false, 4⟩,
      ⟨(.inl .r2d, false), [0, 3], false, 6⟩, ⟨(.inl .r1b, false), [0], true, 5⟩, ⟨(.inl .r2d, false), [1, 3], false, 5⟩, ⟨(.inl .r2d, false), [2, 3], false, 6⟩,
      ⟨(.inl .r1b, false), [3], true, 7⟩, ⟨(.inl .r2d, false), [0, 2], false, 6⟩, ⟨(.inl .r2d, false), [0, 1], false, 5⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 3⟩,
      ⟨(.inl .r3c, true), [0, 1], false, 4⟩, ⟨(.inl .r3c, false), [0, 1], true, 5⟩, ⟨(.inl .r2d, false), [0, 1], false, 4⟩, ⟨(.inl .r2b, false), [0, 1, 2], false, 7⟩,
      ⟨(.inl .r1a, false), [0, 1], true, 6⟩, ⟨(.inl .r2b, false), [2, 3, 0], true, 3⟩, ⟨(.inl .r2b, false), [2, 3, 1], true, 4⟩, ⟨(.inl .r3c, true), [2, 3], false, 5⟩,
      ⟨(.inl .r1a, false), [2, 3], true, 6⟩, ⟨(.inl .r2d, false), [0, 1], true, 3⟩, ⟨(.inl .r2d, false), [0, 3], true, 4⟩, ⟨(.inl .r1b, false), [0], true, 5⟩,
      ⟨(.inl .r2d, false), [1, 3], false, 4⟩, ⟨(.inl .r1b, false), [1], true, 3⟩, ⟨(.inl .r2d, false), [2, 3], false, 3⟩, ⟨(.inl .r1b, false), [3], true, 4⟩]
  | false, false, true, false, false, true, false, false =>
    [⟨(.inl .r1b, false), [0], false, 1⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1b, false), [1], false, 2⟩,
      ⟨(.inl .r2d, false), [0, 1], true, 1⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inl .r2d, false), [0, 1], true, 5⟩, ⟨(.inl .r2d, false), [0, 2], true, 6⟩,
      ⟨(.inl .r2d, false), [0, 3], true, 7⟩, ⟨(.inl .r1b, false), [0], true, 8⟩, ⟨(.inl .r2b, false), [0, 2, 3], false, 7⟩, ⟨(.inl .r3c, true), [0, 2], true, 6⟩,
      ⟨(.inl .r2b, false), [0, 2, 1], false, 5⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], false, 4⟩, ⟨(.inl .r1a, false), [0, 2], true, 3⟩, ⟨(.inl .r2d, false), [0, 1], false, 4⟩,
      ⟨(.inl .r2b, false), [1, 3, 0], true, 3⟩, ⟨(.inl .r3c, true), [1, 3], false, 4⟩, ⟨(.inl .r3c, false), [1, 3], true, 5⟩, ⟨(.inl .r2d, false), [1, 3], false, 4⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 6⟩, ⟨(.inl .r2d, false), [0, 1], true, 3⟩, ⟨(.inl .r2d, false), [0, 3], true, 4⟩, ⟨(.inl .r1b, false), [0], true, 5⟩,
      ⟨(.inl .r2d, false), [1, 3], false, 4⟩, ⟨(.inl .r1b, false), [1], true, 3⟩, ⟨(.inl .r2d, false), [2, 3], false, 3⟩, ⟨(.inl .r1b, false), [3], true, 4⟩]
  | false, false, true, false, false, true, true, true =>
    [⟨(.inl .r1b, false), [0], false, 1⟩, ⟨(.inl .r2d, false), [1, 2], true, 3⟩, ⟨(.inl .r2d, false), [1, 3], true, 4⟩, ⟨(.inl .r2d, false), [0, 2], true, 2⟩,
      ⟨(.inl .r2d, false), [0, 3], true, 3⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inr .k11, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], false, 4⟩,
      ⟨(.inl .r1a, false), [0, 2], true, 3⟩, ⟨(.inl .r1a, false), [1, 3], true, 3⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 2⟩,
      ⟨(.inl .r3c, false), [0, 1], false, 1⟩, ⟨(.inl .r3b, false), [0, 1, 2], true, 0⟩, ⟨(.inl .r1a, false), [2, 3], false, 2⟩, ⟨(.inl .r2b, false), [2, 3, 1], true, 3⟩,
      ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r1a, false), [1, 3], true, 5⟩, ⟨(.inl .r2d, false), [0, 3], false, 6⟩,
      ⟨(.inl .r2d, false), [0, 1], false, 5⟩, ⟨(.inl .r2d, false), [0, 1], true, 5⟩, ⟨(.inl .r2d, false), [0, 3], true, 6⟩, ⟨(.inl .r1b, false), [0], true, 7⟩,
      ⟨(.inl .r2d, false), [1, 3], false, 6⟩, ⟨(.inl .r1b, false), [1], true, 5⟩, ⟨(.inl .r2d, false), [2, 3], false, 5⟩, ⟨(.inl .r1b, false), [3], true, 6⟩]
  | false, false, true, false, true, false, false, false =>
    [⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 2⟩, ⟨(.inl .r3c, false), [0, 1], false, 1⟩, ⟨(.inl .r3b, false), [0, 1, 2], true, 0⟩,
      ⟨(.inl .r1b, false), [0], false, 2⟩, ⟨(.inl .r1a, false), [2, 3], false, 2⟩, ⟨(.inl .r2b, false), [2, 3, 0], true, 3⟩, ⟨(.inl .r1b, false), [3], false, 4⟩,
      ⟨(.inl .r1b, false), [2], false, 4⟩, ⟨(.inl .r2d, false), [2, 3], true, 5⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 11⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 9⟩,
      ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 8⟩, ⟨(.inr .k11, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inl .r1a, false), [1, 3], true, 8⟩, ⟨(.inl .r1a, false), [0, 2], true, 7⟩,
      ⟨(.inl .r2b, false), [1, 3, 0], true, 7⟩, ⟨(.inl .r3c, true), [1, 3], false, 8⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 9⟩, ⟨(.inl .r2d, false), [2, 3], false, 8⟩,
      ⟨(.inl .r3c, false), [1, 3], true, 10⟩, ⟨(.inl .r2d, false), [1, 3], false, 9⟩, ⟨(.inl .r1a, false), [1, 3], true, 11⟩, ⟨(.inl .r2d, false), [1, 2], false, 8⟩,
      ⟨(.inl .r2d, false), [1, 2], true, 8⟩, ⟨(.inl .r2d, false), [1, 3], true, 9⟩, ⟨(.inl .r1b, false), [1], true, 10⟩, ⟨(.inl .r1b, false), [3], true, 9⟩,
      ⟨(.inl .r2d, false), [0, 2], false, 8⟩, ⟨(.inl .r1b, false), [0], true, 7⟩]
  | false, false, true, false, true, false, true, true =>
    [⟨(.inr .k11, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1b, false), [3], false, 2⟩, ⟨(.inl .r1b, false), [2], false, 2⟩,
      ⟨(.inl .r2d, false), [2, 3], true, 3⟩, ⟨(.inr .k11, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], true, 5⟩, ⟨(.inl .r3c, true), [0, 2], false, 6⟩,
      ⟨(.inl .r1a, false), [0, 2], true, 7⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 6⟩, ⟨(.inl .r1a, false), [1, 3], true, 5⟩]
  | false, false, true, false, true, true, false, true =>
    [⟨(.inr .k21, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 3], false, 2⟩, ⟨(.inl .r3c, false), [0, 3], false, 1⟩,
      ⟨(.inl .r2a, false), [0, 3, 1, 2], false, 0⟩, ⟨(.inl .r1b, false), [1], false, 2⟩, ⟨(.inl .r2d, false), [1, 3], true, 3⟩, ⟨(.inl .r1b, false), [0], false, 4⟩,
      ⟨(.inl .r2d, false), [0, 3], false, 3⟩, ⟨(.inl .r2d, false), [0, 1], false, 2⟩, ⟨(.inl .r2b, false), [1, 2, 0], true, 1⟩, ⟨(.inl .r3c, true), [1, 2], false, 2⟩,
      ⟨(.inl .r2b, false), [1, 2, 3], true, 3⟩, ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inr .ksym2, false), [0, 1, 2, 3], true, 4⟩,
      ⟨(.inl .r3b, true), [0, 1, 2], false, 5⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 6⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 6⟩, ⟨(.inl .r3b, false), [1, 2, 3], false, 6⟩,
      ⟨(.inl .r3a, false), [1, 2, 3], false, 6⟩, ⟨(.inl .r2b, false), [1, 3, 0], true, 7⟩, ⟨(.inl .r3c, true), [1, 3], false, 8⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 9⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 8⟩, ⟨(.inl .r3c, false), [1, 3], true, 10⟩, ⟨(.inl .r1a, false), [1, 3], true, 11⟩, ⟨(.inl .r2d, false), [1, 3], false, 9⟩,
      ⟨(.inl .r2d, false), [1, 2], false, 8⟩, ⟨(.inl .r2d, false), [2, 3], true, 9⟩, ⟨(.inl .r3c, false), [2, 3], false, 10⟩, ⟨(.inl .r3c, true), [2, 3], true, 9⟩,
      ⟨(.inl .r2b, false), [2, 3, 1], false, 8⟩, ⟨(.inl .r2b, false), [2, 3, 0], false, 7⟩, ⟨(.inl .r3b, true), [1, 2, 3], true, 6⟩, ⟨(.inl .r2b, false), [1, 3, 0], true, 7⟩,
      ⟨(.inl .r3c, true), [1, 3], false, 8⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 9⟩, ⟨(.inl .r2d, false), [2, 3], false, 8⟩, ⟨(.inl .r3c, false), [1, 3], true, 10⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 11⟩, ⟨(.inl .r2d, false), [1, 3], false, 9⟩, ⟨(.inl .r2d, false), [1, 2], false, 8⟩, ⟨(.inl .r2d, false), [1, 2], true, 8⟩,
      ⟨(.inl .r2d, false), [1, 3], true, 9⟩, ⟨(.inl .r1b, false), [1], true, 10⟩, ⟨(.inl .r2d, false), [2, 3], false, 9⟩, ⟨(.inl .r1b, false), [2], true, 8⟩,
      ⟨(.inl .r2d, false), [0, 3], false, 8⟩, ⟨(.inl .r1b, false), [0], true, 7⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r2b, false), [0, 1, 3], true, 6⟩,
      ⟨(.inl .r1a, false), [0, 1], true, 7⟩, ⟨(.inl .r3c, true), [2, 3], true, 6⟩, ⟨(.inl .r1a, false), [2, 3], true, 5⟩]
  | false, false, true, false, true, true, true, false =>
    [⟨(.inr .k31, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 2], false, 2⟩, ⟨(.inl .r3c, false), [0, 2], false, 1⟩,
      ⟨(.inl .r3b, true), [0, 1, 2], false, 0⟩, ⟨(.inl .r1b, false), [1], false, 2⟩, ⟨(.inl .r2d, false), [1, 2], true, 3⟩, ⟨(.inl .r1b, false), [0], false, 4⟩,
      ⟨(.inl .r2d, false), [0, 2], false, 3⟩, ⟨(.inl .r2d, false), [0, 1], false, 2⟩, ⟨(.inl .r2d, false), [1, 2], true, 3⟩, ⟨(.inl .r1a, false), [1, 3], false, 5⟩,
      ⟨(.inl .r3c, false), [1, 3], false, 4⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 3⟩, ⟨(.inl .r2b, false), [1, 3, 0], false, 2⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 1⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], true, 1⟩, ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 9⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .ksym6, false), [0, 1, 2, 3], true, 6⟩,
      ⟨(.inl .r3b, false), [0, 2, 3], true, 7⟩, ⟨(.inl .r3b, true), [1, 2, 3], false, 8⟩, ⟨(.inl .r2b, false), [2, 3, 0], true, 9⟩, ⟨(.inl .r2b, false), [2, 3, 1], true, 10⟩,
      ⟨(.inl .r3c, true), [2, 3], false, 11⟩, ⟨(.inl .r3c, false), [2, 3], true, 12⟩, ⟨(.inl .r1a, false), [2, 3], true, 13⟩, ⟨(.inl .r2d, false), [2, 3], false, 11⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 12⟩, ⟨(.inl .r1b, false), [2], true, 11⟩, ⟨(.inl .r1b, false), [3], true, 11⟩, ⟨(.inl .r2d, false), [0, 1], false, 10⟩,
      ⟨(.inl .r1b, false), [0], true, 9⟩, ⟨(.inl .r2a, false), [0, 3, 1, 2], true, 7⟩, ⟨(.inl .r2b, false), [0, 3, 1], true, 8⟩, ⟨(.inl .r1a, false), [0, 3], true, 9⟩,
      ⟨(.inl .r3c, false), [1, 2], false, 8⟩, ⟨(.inl .r1a, false), [1, 2], true, 7⟩]
  | false, true, false, false, false, false, false, true =>
    [⟨(.inl .r1b, false), [0], false, 1⟩, ⟨(.inr .k32, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 2⟩,
      ⟨(.inl .r3c, false), [0, 1], false, 1⟩, ⟨(.inl .r3b, false), [0, 1, 2], true, 0⟩, ⟨(.inl .r1b, false), [3], false, 3⟩, ⟨(.inl .r2d, false), [1, 3], true, 2⟩,
      ⟨(.inl .r1a, false), [2, 3], false, 2⟩, ⟨(.inl .r3c, false), [2, 3], true, 3⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .k21, false), [0, 1, 2, 3], true, 5⟩,
      ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r3b, false), [0, 1, 3], true, 5⟩, ⟨(.inl .r3b, false), [1, 2, 3], false, 6⟩, ⟨(.inl .r3a, false), [1, 2, 3], false, 6⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 7⟩, ⟨(.inl .r2d, false), [0, 3], false, 8⟩, ⟨(.inl .r2d, false), [0, 1], false, 7⟩, ⟨(.inl .r2a, false), [0, 3, 1, 2], true, 5⟩,
      ⟨(.inl .r3c, true), [0, 3], false, 6⟩, ⟨(.inl .r2b, false), [0, 3, 1], true, 7⟩, ⟨(.inl .r2d, false), [1, 3], false, 6⟩, ⟨(.inl .r3c, false), [0, 3], true, 8⟩,
      ⟨(.inl .r2d, false), [0, 3], false, 7⟩, ⟨(.inl .r1a, false), [0, 3], true, 9⟩, ⟨(.inl .r2d, false), [0, 1], false, 6⟩, ⟨(.inl .r2b, false), [1, 2, 0], true, 5⟩,
      ⟨(.inl .r3c, true), [1, 2], false, 6⟩, ⟨(.inl .r2b, false), [1, 2, 3], true, 7⟩, ⟨(.inl .r1a, false), [1, 2], true, 8⟩, ⟨(.inl .r2d, false), [0, 2], true, 5⟩,
      ⟨(.inl .r2d, false), [0, 3], true, 6⟩, ⟨(.inl .r1b, false), [0], true, 7⟩, ⟨(.inl .r2d, false), [1, 3], false, 6⟩, ⟨(.inl .r2d, false), [1, 2], false, 5⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 7⟩, ⟨(.inl .r1b, false), [2], true, 6⟩, ⟨(.inl .r1b, false), [3], true, 6⟩]
  | false, true, false, false, false, false, true, false =>
    [⟨(.inl .r1b, false), [0], false, 1⟩, ⟨(.inr .k22, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1b, false), [2], false, 2⟩,
      ⟨(.inl .r2d, false), [0, 2], true, 1⟩, ⟨(.inr .k22, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inl .r2d, false), [0, 1], true, 5⟩, ⟨(.inl .r2d, false), [0, 2], true, 6⟩,
      ⟨(.inl .r2d, false), [0, 3], true, 7⟩, ⟨(.inl .r1b, false), [0], true, 8⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 3⟩, ⟨(.inl .r3c, false), [0, 1], true, 4⟩,
      ⟨(.inl .r2b, false), [0, 1, 2], true, 5⟩, ⟨(.inl .r2b, false), [0, 1, 3], true, 6⟩, ⟨(.inl .r1a, false), [0, 1], true, 7⟩, ⟨(.inl .r2b, false), [2, 3, 0], true, 3⟩,
      ⟨(.inl .r3c, true), [2, 3], false, 4⟩, ⟨(.inl .r3c, false), [2, 3], true, 5⟩, ⟨(.inl .r2d, false), [2, 3], false, 4⟩, ⟨(.inl .r1a, false), [2, 3], true, 6⟩,
      ⟨(.inl .r2d, false), [0, 2], true, 3⟩, ⟨(.inl .r2d, false), [0, 3], true, 4⟩, ⟨(.inl .r1b, false), [0], true, 5⟩, ⟨(.inl .r2d, false), [1, 3], false, 4⟩,
      ⟨(.inl .r2d, false), [1, 2], false, 3⟩, ⟨(.inl .r2d, false), [2, 3], false, 5⟩, ⟨(.inl .r1b, false), [2], true, 4⟩, ⟨(.inl .r1b, false), [3], true, 4⟩]
  | false, true, false, false, false, true, false, false =>
    [⟨(.inl .r1b, false), [0], false, 1⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1b, false), [1], false, 2⟩,
      ⟨(.inl .r2d, false), [0, 1], true, 1⟩, ⟨(.inl .r1a, false), [0, 3], false, 2⟩, ⟨(.inl .r2b, false), [0, 3, 1], false, 1⟩, ⟨(.inl .r2a, false), [0, 3, 1, 2], false, 0⟩,
      ⟨(.inl .r3c, true), [1, 2], false, 1⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 3⟩, ⟨(.inr .ksym2, false), [0, 1, 2, 3], true, 2⟩,
      ⟨(.inl .r3a, false), [1, 2, 3], true, 3⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 3⟩, ⟨(.inl .r1a, false), [2, 3], true, 4⟩, ⟨(.inl .r1a, false), [1, 3], true, 3⟩,
      ⟨(.inl .r2d, false), [1, 2], true, 3⟩, ⟨(.inl .r2b, false), [0, 2, 1], false, 4⟩, ⟨(.inl .r3c, true), [0, 2], true, 3⟩, ⟨(.inl .r3c, false), [1, 3], false, 5⟩,
      ⟨(.inl .r2b, false), [1, 3, 0], false, 4⟩, ⟨(.inl .r2d, false), [0, 3], false, 6⟩, ⟨(.inl .r1b, false), [0], true, 5⟩, ⟨(.inl .r2d, false), [1, 3], false, 5⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 6⟩, ⟨(.inl .r1b, false), [3], true, 7⟩, ⟨(.inl .r2d, false), [0, 2], false, 6⟩, ⟨(.inl .r2d, false), [0, 1], false, 5⟩,
      ⟨(.inl .r2a, false), [0, 2, 1, 3], true, 3⟩, ⟨(.inl .r3c, true), [0, 2], false, 4⟩, ⟨(.inl .r2b, false), [0, 2, 1], true, 5⟩, ⟨(.inl .r2d, false), [1, 2], false, 4⟩,
      ⟨(.inl .r3c, false), [0, 2], true, 6⟩, ⟨(.inl .r2d, false), [0, 2], false, 5⟩, ⟨(.inl .r1a, false), [0, 2], true, 7⟩, ⟨(.inl .r2d, false), [0, 1], false, 4⟩,
      ⟨(.inl .r2b, false), [1, 3, 0], true, 3⟩, ⟨(.inl .r3c, true), [1, 3], false, 4⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 5⟩, ⟨(.inl .r2d, false), [2, 3], false, 4⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 6⟩, ⟨(.inl .r2d, false), [0, 2], true, 3⟩, ⟨(.inl .r2d, false), [0, 3], true, 4⟩, ⟨(.inl .r1b, false), [0], true, 5⟩,
      ⟨(.inl .r2d, false), [1, 3], false, 4⟩, ⟨(.inl .r2d, false), [1, 2], false, 3⟩, ⟨(.inl .r2d, false), [2, 3], false, 5⟩, ⟨(.inl .r1b, false), [2], true, 4⟩,
      ⟨(.inl .r1b, false), [3], true, 4⟩]
  | false, true, false, false, false, true, true, true =>
    [⟨(.inl .r1b, false), [0], false, 1⟩, ⟨(.inl .r2d, false), [1, 2], true, 3⟩, ⟨(.inl .r2d, false), [1, 3], true, 4⟩, ⟨(.inl .r2d, false), [0, 2], true, 2⟩,
      ⟨(.inl .r2d, false), [0, 3], true, 3⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inr .k11, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], false, 4⟩,
      ⟨(.inl .r1a, false), [0, 2], true, 3⟩, ⟨(.inl .r1a, false), [1, 3], true, 3⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 2], false, 2⟩,
      ⟨(.inl .r3c, false), [0, 2], false, 1⟩, ⟨(.inl .r3b, true), [0, 1, 2], false, 0⟩, ⟨(.inl .r1a, false), [1, 3], false, 3⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 2⟩,
      ⟨(.inl .r3a, false), [1, 2, 3], true, 1⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 1⟩, ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inr .ksym6, false), [0, 1, 2, 3], true, 4⟩,
      ⟨(.inl .r1a, false), [2, 3], true, 5⟩, ⟨(.inl .r2d, false), [0, 3], false, 6⟩, ⟨(.inl .r2d, false), [0, 2], false, 5⟩, ⟨(.inl .r2d, false), [0, 2], true, 5⟩,
      ⟨(.inl .r2d, false), [0, 3], true, 6⟩, ⟨(.inl .r1b, false), [0], true, 7⟩, ⟨(.inl .r2d, false), [1, 3], false, 6⟩, ⟨(.inl .r2d, false), [1, 2], false, 5⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 7⟩, ⟨(.inl .r1b, false), [2], true, 6⟩, ⟨(.inl .r1b, false), [3], true, 6⟩]
  | false, true, false, false, true, false, false, false =>
    [⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1b, false), [1], false, 2⟩, ⟨(.inl .r2d, false), [0, 1], true, 1⟩, ⟨(.inl .r1a, false), [0, 2], false, 2⟩,
      ⟨(.inl .r2b, false), [0, 2, 1], false, 1⟩, ⟨(.inl .r3b, true), [0, 1, 2], false, 0⟩, ⟨(.inl .r1b, false), [3], false, 3⟩, ⟨(.inl .r1b, false), [0], false, 4⟩,
      ⟨(.inl .r2d, false), [0, 3], false, 3⟩, ⟨(.inl .r2d, false), [0, 1], false, 2⟩, ⟨(.inl .r2d, false), [1, 3], true, 3⟩, ⟨(.inl .r1a, false), [1, 3], false, 5⟩,
      ⟨(.inl .r3c, false), [1, 3], false, 4⟩, ⟨(.inl .r3c, true), [1, 3], true, 3⟩, ⟨(.inl .r2b, false), [1, 3, 0], false, 2⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 1⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], true, 1⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 10⟩, ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 9⟩, ⟨(.inr .k32, false), [0, 1, 2, 3], true, 7⟩,
      ⟨(.inr .ksym6, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inl .r3b, true), [0, 2, 3], false, 7⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 8⟩, ⟨(.inl .r2b, false), [2, 3, 0], true, 9⟩,
      ⟨(.inl .r2b, false), [2, 3, 1], true, 10⟩, ⟨(.inl .r3c, true), [2, 3], false, 11⟩, ⟨(.inl .r3c, false), [2, 3], true, 12⟩, ⟨(.inl .r1a, false), [2, 3], true, 13⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 11⟩, ⟨(.inl .r2d, false), [2, 3], false, 12⟩, ⟨(.inl .r1b, false), [2], true, 11⟩, ⟨(.inl .r1b, false), [3], true, 11⟩,
      ⟨(.inl .r2a, false), [0, 2, 1, 3], true, 7⟩, ⟨(.inl .r3c, true), [0, 2], false, 8⟩, ⟨(.inl .r2b, false), [0, 2, 1], true, 9⟩, ⟨(.inl .r2d, false), [1, 2], false, 8⟩,
      ⟨(.inl .r1a, false), [0, 2], true, 10⟩, ⟨(.inl .r3c, true), [1, 3], false, 7⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 8⟩, ⟨(.inl .r2d, false), [2, 3], false, 7⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 9⟩, ⟨(.inl .r2d, false), [0, 3], false, 8⟩, ⟨(.inl .r2d, false), [0, 2], false, 7⟩, ⟨(.inl .r2d, false), [1, 3], false, 9⟩,
      ⟨(.inl .r2d, false), [1, 2], false, 8⟩, ⟨(.inl .r2d, false), [2, 3], false, 10⟩, ⟨(.inl .r1b, false), [2], true, 9⟩, ⟨(.inl .r1b, false), [3], true, 9⟩,
      ⟨(.inl .r2d, false), [0, 1], false, 8⟩, ⟨(.inl .r1b, false), [0], true, 7⟩]
  | false, true, false, false, true, false, true, true =>
    [⟨(.inr .k11, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 3], false, 2⟩, ⟨(.inl .r3c, false), [0, 3], false, 1⟩,
      ⟨(.inl .r2a, false), [0, 3, 1, 2], false, 0⟩, ⟨(.inl .r1b, false), [2], false, 2⟩, ⟨(.inl .r2d, false), [2, 3], true, 3⟩, ⟨(.inl .r1b, false), [0], false, 4⟩,
      ⟨(.inl .r2d, false), [0, 3], false, 3⟩, ⟨(.inl .r2d, false), [0, 2], false, 2⟩, ⟨(.inl .r2b, false), [1, 2, 0], true, 1⟩, ⟨(.inl .r3c, false), [1, 2], true, 2⟩,
      ⟨(.inl .r2b, false), [1, 2, 3], true, 3⟩, ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .k22, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inr .ksym2, false), [0, 1, 2, 3], true, 4⟩,
      ⟨(.inl .r3b, false), [0, 1, 2], true, 5⟩, ⟨(.inl .r3b, true), [1, 2, 3], true, 6⟩, ⟨(.inl .r2b, false), [1, 3, 0], true, 7⟩, ⟨(.inl .r3c, true), [1, 3], false, 8⟩,
      ⟨(.inl .r2b, false), [1, 3, 2], true, 9⟩, ⟨(.inl .r2d, false), [2, 3], false, 8⟩, ⟨(.inl .r3c, false), [1, 3], true, 10⟩, ⟨(.inl .r1a, false), [1, 3], true, 11⟩,
      ⟨(.inl .r2d, false), [1, 3], false, 9⟩, ⟨(.inl .r2d, false), [1, 2], false, 8⟩, ⟨(.inl .r2b, false), [2, 3, 0], true, 6⟩, ⟨(.inl .r2b, false), [2, 3, 1], true, 7⟩,
      ⟨(.inl .r3c, true), [2, 3], false, 8⟩, ⟨(.inl .r3c, false), [2, 3], true, 9⟩, ⟨(.inl .r1a, false), [2, 3], true, 10⟩, ⟨(.inl .r2d, false), [2, 3], false, 8⟩,
      ⟨(.inl .r2d, false), [1, 2], true, 7⟩, ⟨(.inl .r2d, false), [1, 3], true, 8⟩, ⟨(.inl .r2d, false), [2, 3], true, 7⟩, ⟨(.inl .r3c, false), [1, 3], false, 9⟩,
      ⟨(.inl .r2b, false), [1, 3, 2], false, 8⟩, ⟨(.inl .r3c, true), [1, 3], true, 7⟩, ⟨(.inl .r2b, false), [1, 3, 0], false, 6⟩, ⟨(.inl .r2d, false), [1, 2], true, 8⟩,
      ⟨(.inl .r2d, false), [1, 3], true, 9⟩, ⟨(.inl .r1b, false), [1], true, 10⟩, ⟨(.inl .r2d, false), [2, 3], false, 9⟩, ⟨(.inl .r1b, false), [2], true, 8⟩,
      ⟨(.inl .r2d, false), [0, 3], false, 8⟩, ⟨(.inl .r1b, false), [0], true, 7⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], true, 5⟩, ⟨(.inl .r2b, false), [0, 2, 3], true, 6⟩,
      ⟨(.inl .r1a, false), [0, 2], true, 7⟩, ⟨(.inl .r3c, true), [1, 3], true, 6⟩, ⟨(.inl .r1a, false), [1, 3], true, 5⟩]
  | false, true, false, false, true, true, false, true =>
    [⟨(.inr .k21, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1b, false), [3], false, 2⟩, ⟨(.inl .r1b, false), [1], false, 2⟩,
      ⟨(.inl .r2d, false), [1, 3], true, 3⟩, ⟨(.inr .k21, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r3c, true), [0, 1], false, 6⟩,
      ⟨(.inl .r1a, false), [0, 1], true, 7⟩, ⟨(.inl .r2b, false), [2, 3, 1], false, 6⟩, ⟨(.inl .r1a, false), [2, 3], true, 5⟩]
  | false, true, false, false, true, true, true, false =>
    [⟨(.inr .k31, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 2⟩, ⟨(.inl .r3c, false), [0, 1], false, 1⟩,
      ⟨(.inl .r3b, false), [0, 1, 2], true, 0⟩, ⟨(.inl .r1b, false), [2], false, 3⟩, ⟨(.inl .r1b, false), [0], false, 4⟩, ⟨(.inl .r2d, false), [0, 2], false, 3⟩,
      ⟨(.inl .r2d, false), [0, 1], false, 2⟩, ⟨(.inl .r1a, false), [2, 3], false, 5⟩, ⟨(.inl .r3c, false), [2, 3], false, 4⟩, ⟨(.inl .r2b, false), [2, 3, 1], false, 3⟩,
      ⟨(.inl .r2b, false), [2, 3, 0], false, 2⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 9⟩, ⟨(.inr .k22, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 6⟩,
      ⟨(.inl .r3b, false), [0, 1, 3], true, 7⟩, ⟨(.inl .r3b, false), [1, 2, 3], false, 8⟩, ⟨(.inl .r3a, false), [1, 2, 3], false, 8⟩, ⟨(.inl .r2b, false), [1, 3, 0], true, 9⟩,
      ⟨(.inl .r3c, true), [1, 3], false, 10⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 11⟩, ⟨(.inl .r2d, false), [2, 3], false, 10⟩, ⟨(.inl .r3c, false), [1, 3], true, 12⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 13⟩, ⟨(.inl .r2d, false), [1, 3], false, 11⟩, ⟨(.inl .r2d, false), [1, 2], false, 10⟩, ⟨(.inl .r2d, false), [1, 2], true, 10⟩,
      ⟨(.inl .r2d, false), [1, 3], true, 11⟩, ⟨(.inl .r1b, false), [1], true, 12⟩, ⟨(.inl .r1b, false), [3], true, 11⟩, ⟨(.inl .r2d, false), [0, 2], false, 10⟩,
      ⟨(.inl .r1b, false), [0], true, 9⟩, ⟨(.inl .r2a, false), [0, 3, 1, 2], true, 7⟩, ⟨(.inl .r2b, false), [0, 3, 2], true, 8⟩, ⟨(.inl .r1a, false), [0, 3], true, 9⟩,
      ⟨(.inl .r3c, true), [1, 2], true, 8⟩, ⟨(.inl .r1a, false), [1, 2], true, 7⟩]
  | false, true, true, true, false, false, false, true =>
    [⟨(.inl .r1b, false), [0], false, 1⟩, ⟨(.inr .k32, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 3], false, 2⟩,
      ⟨(.inl .r3c, false), [0, 3], false, 1⟩, ⟨(.inl .r2a, false), [0, 3, 1, 2], false, 0⟩, ⟨(.inl .r1b, false), [0], false, 2⟩, ⟨(.inl .r2b, false), [1, 2, 0], true, 1⟩,
      ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inr .k32, false), [0, 1, 2, 3], true, 3⟩, ⟨(.inr .ksym2, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inl .r2a, false), [0, 3, 1, 2], false, 3⟩,
      ⟨(.inl .r1a, false), [1, 2], true, 4⟩, ⟨(.inl .r2d, false), [1, 2], true, 5⟩, ⟨(.inl .r2d, false), [1, 3], true, 6⟩, ⟨(.inl .r2d, false), [2, 3], true, 5⟩,
      ⟨(.inl .r3c, false), [1, 3], false, 7⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 6⟩, ⟨(.inl .r3c, true), [1, 3], true, 5⟩, ⟨(.inl .r2b, false), [1, 3, 0], false, 4⟩,
      ⟨(.inl .r2d, false), [2, 3], true, 7⟩, ⟨(.inl .r3c, false), [2, 3], false, 8⟩, ⟨(.inl .r3c, true), [2, 3], true, 7⟩, ⟨(.inl .r2b, false), [2, 3, 1], false, 6⟩,
      ⟨(.inl .r2b, false), [2, 3, 0], false, 5⟩, ⟨(.inl .r3b, false), [1, 2, 3], false, 4⟩, ⟨(.inl .r3a, false), [1, 2, 3], false, 4⟩, ⟨(.inl .r2b, false), [1, 3, 0], true, 5⟩,
      ⟨(.inl .r3c, true), [1, 3], false, 6⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 7⟩, ⟨(.inl .r2d, false), [2, 3], false, 6⟩, ⟨(.inl .r3c, false), [1, 3], true, 8⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 9⟩, ⟨(.inl .r2d, false), [1, 3], false, 7⟩, ⟨(.inl .r2d, false), [1, 2], false, 6⟩, ⟨(.inl .r2d, false), [1, 2], true, 6⟩,
      ⟨(.inl .r2d, false), [1, 3], true, 7⟩, ⟨(.inl .r1b, false), [1], true, 8⟩, ⟨(.inl .r2d, false), [2, 3], false, 7⟩, ⟨(.inl .r1b, false), [2], true, 6⟩,
      ⟨(.inl .r2d, false), [0, 3], false, 6⟩, ⟨(.inl .r1b, false), [0], true, 5⟩, ⟨(.inl .r2a, false), [0, 3, 1, 2], true, 3⟩, ⟨(.inl .r3c, false), [0, 3], true, 4⟩,
      ⟨(.inl .r1a, false), [0, 3], true, 5⟩, ⟨(.inl .r2b, false), [1, 2, 0], false, 4⟩, ⟨(.inl .r1a, false), [1, 2], true, 3⟩, ⟨(.inl .r1b, false), [0], true, 3⟩]
  | false, true, true, true, false, false, true, false =>
    [⟨(.inl .r1b, false), [0], false, 1⟩, ⟨(.inr .k22, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 2], false, 2⟩,
      ⟨(.inl .r3c, false), [0, 2], false, 1⟩, ⟨(.inl .r3b, true), [0, 1, 2], false, 0⟩, ⟨(.inl .r1b, false), [0], false, 2⟩, ⟨(.inl .r1a, false), [1, 3], false, 3⟩,
      ⟨(.inl .r2b, false), [1, 3, 0], false, 2⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 1⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 1⟩, ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 7⟩,
      ⟨(.inr .k22, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inr .ksym6, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], false, 5⟩, ⟨(.inl .r1a, false), [2, 3], true, 6⟩,
      ⟨(.inl .r2d, false), [2, 3], true, 8⟩, ⟨(.inl .r3c, false), [2, 3], false, 9⟩, ⟨(.inl .r3c, true), [2, 3], true, 8⟩, ⟨(.inl .r2b, false), [2, 3, 1], false, 7⟩,
      ⟨(.inl .r2b, false), [2, 3, 0], false, 6⟩, ⟨(.inl .r2d, false), [2, 3], false, 10⟩, ⟨(.inl .r1b, false), [2], true, 9⟩, ⟨(.inl .r1b, false), [3], true, 9⟩,
      ⟨(.inl .r2d, false), [0, 1], false, 8⟩, ⟨(.inl .r1b, false), [0], true, 7⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r3c, false), [0, 1], true, 6⟩,
      ⟨(.inl .r1a, false), [0, 1], true, 7⟩, ⟨(.inl .r2b, false), [2, 3, 0], false, 6⟩, ⟨(.inl .r1a, false), [2, 3], true, 5⟩, ⟨(.inl .r1b, false), [0], true, 5⟩]
  | false, true, true, true, false, true, false, false =>
    [⟨(.inl .r1b, false), [0], false, 1⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 2⟩,
      ⟨(.inl .r3c, false), [0, 1], false, 1⟩, ⟨(.inl .r3b, false), [0, 1, 2], true, 0⟩, ⟨(.inl .r1b, false), [0], false, 2⟩, ⟨(.inl .r1a, false), [2, 3], false, 2⟩,
      ⟨(.inl .r2b, false), [2, 3, 0], true, 3⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 4⟩,
      ⟨(.inl .r2a, false), [0, 2, 1, 3], false, 5⟩, ⟨(.inl .r1a, false), [1, 3], true, 6⟩, ⟨(.inl .r2d, false), [1, 2], true, 7⟩, ⟨(.inl .r2d, false), [1, 3], true, 8⟩,
      ⟨(.inl .r2d, false), [2, 3], true, 7⟩, ⟨(.inl .r3c, false), [1, 3], false, 9⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 8⟩, ⟨(.inl .r3c, true), [1, 3], true, 7⟩,
      ⟨(.inl .r2b, false), [1, 3, 0], false, 6⟩, ⟨(.inl .r2d, false), [1, 2], true, 8⟩, ⟨(.inl .r2d, false), [1, 3], true, 9⟩, ⟨(.inl .r1b, false), [1], true, 10⟩,
      ⟨(.inl .r1b, false), [3], true, 9⟩, ⟨(.inl .r2d, false), [0, 2], false, 8⟩, ⟨(.inl .r1b, false), [0], true, 7⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], true, 5⟩,
      ⟨(.inl .r3c, false), [0, 2], true, 6⟩, ⟨(.inl .r1a, false), [0, 2], true, 7⟩, ⟨(.inl .r2b, false), [1, 3, 0], false, 6⟩, ⟨(.inl .r1a, false), [1, 3], true, 5⟩,
      ⟨(.inl .r1b, false), [0], true, 5⟩]
  | false, true, true, true, false, true, true, true =>
    [⟨(.inl .r1b, false), [0], false, 1⟩, ⟨(.inl .r2d, false), [1, 2], true, 3⟩, ⟨(.inl .r2d, false), [1, 3], true, 4⟩, ⟨(.inl .r2d, false), [0, 2], true, 2⟩,
      ⟨(.inl .r2d, false), [0, 3], true, 3⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inr .k11, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], false, 4⟩,
      ⟨(.inl .r1a, false), [0, 2], true, 3⟩, ⟨(.inl .r1a, false), [1, 3], true, 3⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1b, false), [0], true, 3⟩]
  | false, true, true, true, true, false, false, false =>
    [⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1b, false), [1], false, 2⟩, ⟨(.inl .r2d, false), [0, 1], true, 1⟩, ⟨(.inl .r1b, false), [3], false, 2⟩,
      ⟨(.inl .r1b, false), [2], false, 2⟩, ⟨(.inl .r2d, false), [2, 3], true, 3⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inr .k11, false), [0, 1, 2, 3], true, 4⟩,
      ⟨(.inl .r2a, false), [0, 2, 1, 3], false, 6⟩, ⟨(.inl .r1a, false), [0, 2], true, 5⟩, ⟨(.inl .r1a, false), [1, 3], true, 5⟩, ⟨(.inl .r2d, false), [0, 1], true, 5⟩,
      ⟨(.inl .r2d, false), [0, 2], true, 6⟩, ⟨(.inl .r2d, false), [0, 3], true, 7⟩, ⟨(.inl .r1b, false), [0], true, 8⟩]
  | false, true, true, true, true, false, true, true =>
    [⟨(.inr .k11, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 2⟩, ⟨(.inl .r3c, false), [0, 1], false, 1⟩,
      ⟨(.inl .r3b, false), [0, 1, 2], true, 0⟩, ⟨(.inl .r1a, false), [2, 3], false, 2⟩, ⟨(.inl .r2b, false), [2, 3, 1], true, 3⟩, ⟨(.inl .r1b, false), [3], false, 4⟩,
      ⟨(.inl .r1b, false), [2], false, 4⟩, ⟨(.inl .r2d, false), [2, 3], true, 5⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 9⟩, ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 8⟩,
      ⟨(.inr .k11, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inl .r1a, false), [1, 3], true, 8⟩, ⟨(.inl .r2d, false), [0, 3], false, 10⟩, ⟨(.inl .r2d, false), [0, 1], false, 9⟩,
      ⟨(.inl .r2b, false), [0, 2, 3], false, 11⟩, ⟨(.inl .r2b, false), [0, 2, 1], false, 10⟩, ⟨(.inl .r3c, false), [0, 2], false, 9⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], false, 8⟩,
      ⟨(.inl .r1a, false), [0, 2], true, 7⟩, ⟨(.inl .r2d, false), [1, 2], false, 8⟩, ⟨(.inl .r3c, true), [1, 3], false, 7⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 8⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 7⟩, ⟨(.inl .r3c, false), [1, 3], true, 9⟩, ⟨(.inl .r2d, false), [1, 3], false, 8⟩, ⟨(.inl .r1a, false), [1, 3], true, 10⟩,
      ⟨(.inl .r2d, false), [1, 2], false, 7⟩]
  | false, true, true, true, true, true, false, true =>
    [⟨(.inr .k21, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 2], false, 2⟩, ⟨(.inl .r3c, false), [0, 2], false, 1⟩,
      ⟨(.inl .r3b, true), [0, 1, 2], false, 0⟩, ⟨(.inl .r1a, false), [1, 3], false, 3⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 2⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 1⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], true, 1⟩, ⟨(.inl .r1b, false), [3], false, 4⟩, ⟨(.inl .r1b, false), [1], false, 5⟩, ⟨(.inl .r2d, false), [1, 3], false, 4⟩,
      ⟨(.inl .r2d, false), [1, 2], false, 3⟩, ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 9⟩, ⟨(.inr .ksym6, false), [0, 1, 2, 3], true, 8⟩, ⟨(.inr .k21, false), [0, 1, 2, 3], true, 6⟩,
      ⟨(.inl .r1a, false), [2, 3], true, 8⟩, ⟨(.inl .r2d, false), [0, 3], false, 10⟩, ⟨(.inl .r2d, false), [0, 2], false, 9⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 7⟩,
      ⟨(.inl .r3c, true), [0, 1], false, 8⟩, ⟨(.inl .r2b, false), [0, 1, 2], true, 9⟩, ⟨(.inl .r2b, false), [0, 1, 3], true, 10⟩, ⟨(.inl .r1a, false), [0, 1], true, 11⟩,
      ⟨(.inl .r2b, false), [2, 3, 1], true, 7⟩, ⟨(.inl .r3c, true), [2, 3], false, 8⟩, ⟨(.inl .r3c, false), [2, 3], true, 9⟩, ⟨(.inl .r2d, false), [2, 3], false, 8⟩,
      ⟨(.inl .r1a, false), [2, 3], true, 10⟩]
  | false, true, true, true, true, true, true, false =>
    [⟨(.inr .k31, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 3], false, 2⟩, ⟨(.inl .r3c, false), [0, 3], false, 1⟩,
      ⟨(.inl .r2a, false), [0, 3, 1, 2], false, 0⟩, ⟨(.inl .r2b, false), [1, 2, 3], true, 1⟩, ⟨(.inl .r1b, false), [2], false, 1⟩, ⟨(.inl .r2d, false), [2, 3], true, 2⟩,
      ⟨(.inl .r1b, false), [1], false, 3⟩, ⟨(.inl .r2d, false), [1, 3], false, 2⟩, ⟨(.inl .r2d, false), [1, 2], false, 1⟩, ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 7⟩,
      ⟨(.inr .ksym2, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inr .k31, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r1a, false), [1, 2], true, 6⟩, ⟨(.inl .r3b, false), [1, 2, 3], false, 6⟩,
      ⟨(.inl .r3a, false), [1, 2, 3], false, 6⟩, ⟨(.inl .r1a, false), [1, 3], true, 7⟩, ⟨(.inl .r2d, false), [0, 2], false, 8⟩, ⟨(.inl .r2d, false), [0, 1], false, 7⟩,
      ⟨(.inl .r2a, false), [0, 3, 1, 2], true, 5⟩, ⟨(.inl .r3c, true), [0, 3], false, 6⟩, ⟨(.inl .r2b, false), [0, 3, 1], true, 7⟩, ⟨(.inl .r2d, false), [1, 3], false, 6⟩,
      ⟨(.inl .r2b, false), [0, 3, 2], true, 8⟩, ⟨(.inl .r1a, false), [0, 3], true, 9⟩, ⟨(.inl .r2d, false), [2, 3], false, 7⟩, ⟨(.inl .r3c, true), [1, 2], false, 5⟩,
      ⟨(.inl .r3c, false), [1, 2], true, 6⟩, ⟨(.inl .r2d, false), [1, 2], false, 5⟩, ⟨(.inl .r2b, false), [1, 2, 3], true, 7⟩, ⟨(.inl .r1a, false), [1, 2], true, 8⟩]
  | true, false, false, false, false, false, false, true =>
    [⟨(.inl .r1b, false), [0], false, 1⟩, ⟨(.inr .k32, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 3], false, 2⟩,
      ⟨(.inl .r3c, false), [0, 3], false, 1⟩, ⟨(.inl .r2a, false), [0, 3, 1, 2], false, 0⟩, ⟨(.inl .r2b, false), [1, 2, 3], true, 1⟩, ⟨(.inl .r1b, false), [2], false, 1⟩,
      ⟨(.inl .r2d, false), [2, 3], true, 2⟩, ⟨(.inl .r1b, false), [1], false, 3⟩, ⟨(.inl .r2d, false), [1, 3], false, 2⟩, ⟨(.inl .r2d, false), [1, 2], false, 1⟩,
      ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .ksym2, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inr .k31, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r1a, false), [1, 2], true, 6⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], false, 6⟩, ⟨(.inl .r3a, false), [1, 2, 3], false, 6⟩, ⟨(.inl .r1a, false), [1, 3], true, 7⟩, ⟨(.inl .r2d, false), [0, 2], false, 8⟩,
      ⟨(.inl .r2d, false), [0, 1], false, 7⟩, ⟨(.inl .r2a, false), [0, 3, 1, 2], true, 5⟩, ⟨(.inl .r3c, true), [0, 3], false, 6⟩, ⟨(.inl .r2b, false), [0, 3, 1], true, 7⟩,
      ⟨(.inl .r2d, false), [1, 3], false, 6⟩, ⟨(.inl .r2b, false), [0, 3, 2], true, 8⟩, ⟨(.inl .r1a, false), [0, 3], true, 9⟩, ⟨(.inl .r2d, false), [2, 3], false, 7⟩,
      ⟨(.inl .r3c, true), [1, 2], false, 5⟩, ⟨(.inl .r3c, false), [1, 2], true, 6⟩, ⟨(.inl .r2d, false), [1, 2], false, 5⟩, ⟨(.inl .r2b, false), [1, 2, 3], true, 7⟩,
      ⟨(.inl .r1a, false), [1, 2], true, 8⟩, ⟨(.inl .r2d, false), [0, 3], false, 7⟩, ⟨(.inl .r2d, false), [0, 2], false, 6⟩, ⟨(.inl .r2d, false), [0, 1], false, 5⟩,
      ⟨(.inl .r2d, false), [1, 2], true, 6⟩, ⟨(.inl .r2d, false), [1, 3], true, 7⟩, ⟨(.inl .r1b, false), [1], true, 8⟩, ⟨(.inl .r2d, false), [2, 3], false, 7⟩,
      ⟨(.inl .r1b, false), [2], true, 6⟩, ⟨(.inl .r1b, false), [3], true, 6⟩]
  | true, false, false, false, false, false, true, false =>
    [⟨(.inl .r1b, false), [0], false, 1⟩, ⟨(.inr .k22, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 2], false, 2⟩,
      ⟨(.inl .r3c, false), [0, 2], false, 1⟩, ⟨(.inl .r3b, true), [0, 1, 2], false, 0⟩, ⟨(.inl .r1a, false), [1, 3], false, 3⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 2⟩,
      ⟨(.inl .r3a, false), [1, 2, 3], true, 1⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 1⟩, ⟨(.inl .r1b, false), [3], false, 4⟩, ⟨(.inl .r1b, false), [1], false, 5⟩,
      ⟨(.inl .r2d, false), [1, 3], false, 4⟩, ⟨(.inl .r2d, false), [1, 2], false, 3⟩, ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 9⟩, ⟨(.inr .ksym6, false), [0, 1, 2, 3], true, 8⟩,
      ⟨(.inr .k21, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inl .r1a, false), [2, 3], true, 8⟩, ⟨(.inl .r2d, false), [0, 3], false, 10⟩, ⟨(.inl .r2d, false), [0, 2], false, 9⟩,
      ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inl .r3c, true), [0, 1], false, 8⟩, ⟨(.inl .r2b, false), [0, 1, 2], true, 9⟩, ⟨(.inl .r2b, false), [0, 1, 3], true, 10⟩,
      ⟨(.inl .r1a, false), [0, 1], true, 11⟩, ⟨(.inl .r2b, false), [2, 3, 1], true, 7⟩, ⟨(.inl .r3c, true), [2, 3], false, 8⟩, ⟨(.inl .r3c, false), [2, 3], true, 9⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 8⟩, ⟨(.inl .r1a, false), [2, 3], true, 10⟩, ⟨(.inl .r2d, false), [0, 3], false, 9⟩, ⟨(.inl .r2d, false), [0, 2], false, 8⟩,
      ⟨(.inl .r2d, false), [0, 1], false, 7⟩, ⟨(.inl .r2d, false), [1, 2], true, 8⟩, ⟨(.inl .r2d, false), [1, 3], true, 9⟩, ⟨(.inl .r1b, false), [1], true, 10⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 9⟩, ⟨(.inl .r1b, false), [2], true, 8⟩, ⟨(.inl .r1b, false), [3], true, 8⟩]
  | true, false, false, false, false, true, false, false =>
    [⟨(.inl .r1b, false), [0], false, 1⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 2⟩,
      ⟨(.inl .r3c, false), [0, 1], false, 1⟩, ⟨(.inl .r3b, false), [0, 1, 2], true, 0⟩, ⟨(.inl .r1a, false), [2, 3], false, 2⟩, ⟨(.inl .r2b, false), [2, 3, 1], true, 3⟩,
      ⟨(.inl .r1b, false), [3], false, 4⟩, ⟨(.inl .r1b, false), [2], false, 4⟩, ⟨(.inl .r2d, false), [2, 3], true, 5⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 9⟩,
      ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 8⟩, ⟨(.inr .k11, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inl .r1a, false), [1, 3], true, 8⟩, ⟨(.inl .r2d, false), [0, 3], false, 10⟩,
      ⟨(.inl .r2d, false), [0, 1], false, 9⟩, ⟨(.inl .r2b, false), [0, 2, 3], false, 11⟩, ⟨(.inl .r2b, false), [0, 2, 1], false, 10⟩, ⟨(.inl .r3c, false), [0, 2], false, 9⟩,
      ⟨(.inl .r2a, false), [0, 2, 1, 3], false, 8⟩, ⟨(.inl .r1a, false), [0, 2], true, 7⟩, ⟨(.inl .r2d, false), [1, 2], false, 8⟩, ⟨(.inl .r3c, true), [1, 3], false, 7⟩,
      ⟨(.inl .r2b, false), [1, 3, 2], true, 8⟩, ⟨(.inl .r2d, false), [2, 3], false, 7⟩, ⟨(.inl .r3c, false), [1, 3], true, 9⟩, ⟨(.inl .r2d, false), [1, 3], false, 8⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 10⟩, ⟨(.inl .r2d, false), [1, 2], false, 7⟩, ⟨(.inl .r2d, false), [0, 3], false, 9⟩, ⟨(.inl .r2d, false), [0, 2], false, 8⟩,
      ⟨(.inl .r2d, false), [0, 1], false, 7⟩, ⟨(.inl .r2d, false), [1, 2], true, 8⟩, ⟨(.inl .r2d, false), [1, 3], true, 9⟩, ⟨(.inl .r1b, false), [1], true, 10⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 9⟩, ⟨(.inl .r1b, false), [2], true, 8⟩, ⟨(.inl .r1b, false), [3], true, 8⟩]
  | true, false, false, false, false, true, true, true =>
    [⟨(.inl .r1b, false), [0], false, 1⟩, ⟨(.inl .r2d, false), [1, 2], true, 3⟩, ⟨(.inl .r2d, false), [1, 3], true, 4⟩, ⟨(.inl .r2d, false), [0, 2], true, 2⟩,
      ⟨(.inl .r2d, false), [0, 3], true, 3⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inr .k11, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], false, 4⟩,
      ⟨(.inl .r1a, false), [0, 2], true, 3⟩, ⟨(.inl .r1a, false), [1, 3], true, 3⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1b, false), [1], false, 2⟩,
      ⟨(.inl .r2d, false), [0, 1], true, 1⟩, ⟨(.inl .r1b, false), [3], false, 2⟩, ⟨(.inl .r1b, false), [2], false, 2⟩, ⟨(.inl .r2d, false), [2, 3], true, 3⟩,
      ⟨(.inr .k12, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inr .k11, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], false, 6⟩, ⟨(.inl .r1a, false), [0, 2], true, 5⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 5⟩, ⟨(.inl .r2d, false), [0, 1], true, 5⟩, ⟨(.inl .r2d, false), [0, 2], true, 6⟩, ⟨(.inl .r2d, false), [0, 3], true, 7⟩,
      ⟨(.inl .r1b, false), [0], true, 8⟩, ⟨(.inl .r2d, false), [0, 3], false, 7⟩, ⟨(.inl .r2d, false), [0, 2], false, 6⟩, ⟨(.inl .r2d, false), [0, 1], false, 5⟩,
      ⟨(.inl .r2d, false), [1, 2], true, 6⟩, ⟨(.inl .r2d, false), [1, 3], true, 7⟩, ⟨(.inl .r1b, false), [1], true, 8⟩, ⟨(.inl .r2d, false), [2, 3], false, 7⟩,
      ⟨(.inl .r1b, false), [2], true, 6⟩, ⟨(.inl .r1b, false), [3], true, 6⟩]
  | true, false, false, false, true, false, false, false =>
    [⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩]
  | true, false, false, false, true, false, true, true =>
    [⟨(.inr .k11, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 2⟩, ⟨(.inl .r3c, false), [0, 1], false, 1⟩,
      ⟨(.inl .r3b, false), [0, 1, 2], true, 0⟩, ⟨(.inl .r1b, false), [0], false, 2⟩, ⟨(.inl .r1a, false), [2, 3], false, 2⟩, ⟨(.inl .r2b, false), [2, 3, 0], true, 3⟩,
      ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], false, 5⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 6⟩, ⟨(.inl .r2d, false), [1, 2], true, 7⟩, ⟨(.inl .r2d, false), [1, 3], true, 8⟩, ⟨(.inl .r2d, false), [2, 3], true, 7⟩,
      ⟨(.inl .r3c, false), [1, 3], false, 9⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 8⟩, ⟨(.inl .r3c, true), [1, 3], true, 7⟩, ⟨(.inl .r2b, false), [1, 3, 0], false, 6⟩,
      ⟨(.inl .r2d, false), [1, 2], true, 8⟩, ⟨(.inl .r2d, false), [1, 3], true, 9⟩, ⟨(.inl .r1b, false), [1], true, 10⟩, ⟨(.inl .r1b, false), [3], true, 9⟩,
      ⟨(.inl .r2d, false), [0, 2], false, 8⟩, ⟨(.inl .r1b, false), [0], true, 7⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], true, 5⟩, ⟨(.inl .r3c, false), [0, 2], true, 6⟩,
      ⟨(.inl .r1a, false), [0, 2], true, 7⟩, ⟨(.inl .r2b, false), [1, 3, 0], false, 6⟩, ⟨(.inl .r1a, false), [1, 3], true, 5⟩]
  | true, false, false, false, true, true, false, true =>
    [⟨(.inr .k21, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 2], false, 2⟩, ⟨(.inl .r3c, false), [0, 2], false, 1⟩,
      ⟨(.inl .r3b, true), [0, 1, 2], false, 0⟩, ⟨(.inl .r1b, false), [0], false, 2⟩, ⟨(.inl .r1a, false), [1, 3], false, 3⟩, ⟨(.inl .r2b, false), [1, 3, 0], false, 2⟩,
      ⟨(.inl .r3a, false), [1, 2, 3], true, 1⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 1⟩, ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .k22, false), [0, 1, 2, 3], true, 5⟩,
      ⟨(.inr .ksym6, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], false, 5⟩, ⟨(.inl .r1a, false), [2, 3], true, 6⟩, ⟨(.inl .r2d, false), [2, 3], true, 8⟩,
      ⟨(.inl .r3c, false), [2, 3], false, 9⟩, ⟨(.inl .r3c, true), [2, 3], true, 8⟩, ⟨(.inl .r2b, false), [2, 3, 1], false, 7⟩, ⟨(.inl .r2b, false), [2, 3, 0], false, 6⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 10⟩, ⟨(.inl .r1b, false), [2], true, 9⟩, ⟨(.inl .r1b, false), [3], true, 9⟩, ⟨(.inl .r2d, false), [0, 1], false, 8⟩,
      ⟨(.inl .r1b, false), [0], true, 7⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r3c, false), [0, 1], true, 6⟩, ⟨(.inl .r1a, false), [0, 1], true, 7⟩,
      ⟨(.inl .r2b, false), [2, 3, 0], false, 6⟩, ⟨(.inl .r1a, false), [2, 3], true, 5⟩]
  | true, false, false, false, true, true, true, false =>
    [⟨(.inr .k31, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 3], false, 2⟩, ⟨(.inl .r3c, false), [0, 3], false, 1⟩,
      ⟨(.inl .r2a, false), [0, 3, 1, 2], false, 0⟩, ⟨(.inl .r1b, false), [0], false, 2⟩, ⟨(.inl .r2b, false), [1, 2, 0], true, 1⟩, ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 5⟩,
      ⟨(.inr .k32, false), [0, 1, 2, 3], true, 3⟩, ⟨(.inr .ksym2, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inl .r2a, false), [0, 3, 1, 2], false, 3⟩, ⟨(.inl .r1a, false), [1, 2], true, 4⟩,
      ⟨(.inl .r2d, false), [1, 2], true, 5⟩, ⟨(.inl .r2d, false), [1, 3], true, 6⟩, ⟨(.inl .r2d, false), [2, 3], true, 5⟩, ⟨(.inl .r3c, false), [1, 3], false, 7⟩,
      ⟨(.inl .r2b, false), [1, 3, 2], false, 6⟩, ⟨(.inl .r3c, true), [1, 3], true, 5⟩, ⟨(.inl .r2b, false), [1, 3, 0], false, 4⟩, ⟨(.inl .r2d, false), [2, 3], true, 7⟩,
      ⟨(.inl .r3c, false), [2, 3], false, 8⟩, ⟨(.inl .r3c, true), [2, 3], true, 7⟩, ⟨(.inl .r2b, false), [2, 3, 1], false, 6⟩, ⟨(.inl .r2b, false), [2, 3, 0], false, 5⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], false, 4⟩, ⟨(.inl .r3a, false), [1, 2, 3], false, 4⟩, ⟨(.inl .r2b, false), [1, 3, 0], true, 5⟩, ⟨(.inl .r3c, true), [1, 3], false, 6⟩,
      ⟨(.inl .r2b, false), [1, 3, 2], true, 7⟩, ⟨(.inl .r2d, false), [2, 3], false, 6⟩, ⟨(.inl .r3c, false), [1, 3], true, 8⟩, ⟨(.inl .r1a, false), [1, 3], true, 9⟩,
      ⟨(.inl .r2d, false), [1, 3], false, 7⟩, ⟨(.inl .r2d, false), [1, 2], false, 6⟩, ⟨(.inl .r2d, false), [1, 2], true, 6⟩, ⟨(.inl .r2d, false), [1, 3], true, 7⟩,
      ⟨(.inl .r1b, false), [1], true, 8⟩, ⟨(.inl .r2d, false), [2, 3], false, 7⟩, ⟨(.inl .r1b, false), [2], true, 6⟩, ⟨(.inl .r2d, false), [0, 3], false, 6⟩,
      ⟨(.inl .r1b, false), [0], true, 5⟩, ⟨(.inl .r2a, false), [0, 3, 1, 2], true, 3⟩, ⟨(.inl .r3c, false), [0, 3], true, 4⟩, ⟨(.inl .r1a, false), [0, 3], true, 5⟩,
      ⟨(.inl .r2b, false), [1, 2, 0], false, 4⟩, ⟨(.inl .r1a, false), [1, 2], true, 3⟩]
  | true, false, true, true, false, false, false, true =>
    [⟨(.inl .r1b, false), [0], false, 1⟩, ⟨(.inr .k32, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 2⟩,
      ⟨(.inl .r3c, false), [0, 1], false, 1⟩, ⟨(.inl .r3b, false), [0, 1, 2], true, 0⟩, ⟨(.inl .r1b, false), [2], false, 3⟩, ⟨(.inl .r1b, false), [0], false, 4⟩,
      ⟨(.inl .r2d, false), [0, 2], false, 3⟩, ⟨(.inl .r2d, false), [0, 1], false, 2⟩, ⟨(.inl .r1a, false), [2, 3], false, 5⟩, ⟨(.inl .r3c, false), [2, 3], false, 4⟩,
      ⟨(.inl .r2b, false), [2, 3, 1], false, 3⟩, ⟨(.inl .r2b, false), [2, 3, 0], false, 2⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 9⟩, ⟨(.inr .k22, false), [0, 1, 2, 3], true, 7⟩,
      ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inl .r3b, false), [0, 1, 3], true, 7⟩, ⟨(.inl .r3b, false), [1, 2, 3], false, 8⟩, ⟨(.inl .r3a, false), [1, 2, 3], false, 8⟩,
      ⟨(.inl .r2b, false), [1, 3, 0], true, 9⟩, ⟨(.inl .r3c, true), [1, 3], false, 10⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 11⟩, ⟨(.inl .r2d, false), [2, 3], false, 10⟩,
      ⟨(.inl .r3c, false), [1, 3], true, 12⟩, ⟨(.inl .r1a, false), [1, 3], true, 13⟩, ⟨(.inl .r2d, false), [1, 3], false, 11⟩, ⟨(.inl .r2d, false), [1, 2], false, 10⟩,
      ⟨(.inl .r2d, false), [1, 2], true, 10⟩, ⟨(.inl .r2d, false), [1, 3], true, 11⟩, ⟨(.inl .r1b, false), [1], true, 12⟩, ⟨(.inl .r1b, false), [3], true, 11⟩,
      ⟨(.inl .r2d, false), [0, 2], false, 10⟩, ⟨(.inl .r1b, false), [0], true, 9⟩, ⟨(.inl .r2a, false), [0, 3, 1, 2], true, 7⟩, ⟨(.inl .r2b, false), [0, 3, 2], true, 8⟩,
      ⟨(.inl .r1a, false), [0, 3], true, 9⟩, ⟨(.inl .r3c, true), [1, 2], true, 8⟩, ⟨(.inl .r1a, false), [1, 2], true, 7⟩, ⟨(.inl .r2d, false), [0, 1], false, 7⟩,
      ⟨(.inl .r1b, false), [1], true, 8⟩]
  | true, false, true, true, false, false, true, false =>
    [⟨(.inl .r1b, false), [0], false, 1⟩, ⟨(.inr .k22, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1b, false), [3], false, 2⟩,
      ⟨(.inl .r1b, false), [1], false, 2⟩, ⟨(.inl .r2d, false), [1, 3], true, 3⟩, ⟨(.inr .k21, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 5⟩,
      ⟨(.inl .r3c, true), [0, 1], false, 6⟩, ⟨(.inl .r1a, false), [0, 1], true, 7⟩, ⟨(.inl .r2b, false), [2, 3, 1], false, 6⟩, ⟨(.inl .r1a, false), [2, 3], true, 5⟩,
      ⟨(.inl .r2d, false), [0, 1], false, 5⟩, ⟨(.inl .r1b, false), [1], true, 6⟩]
  | true, false, true, true, false, true, false, false =>
    [⟨(.inl .r1b, false), [0], false, 1⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 3], false, 2⟩,
      ⟨(.inl .r3c, false), [0, 3], false, 1⟩, ⟨(.inl .r2a, false), [0, 3, 1, 2], false, 0⟩, ⟨(.inl .r1b, false), [2], false, 2⟩, ⟨(.inl .r2d, false), [2, 3], true, 3⟩,
      ⟨(.inl .r1b, false), [0], false, 4⟩, ⟨(.inl .r2d, false), [0, 3], false, 3⟩, ⟨(.inl .r2d, false), [0, 2], false, 2⟩, ⟨(.inl .r2b, false), [1, 2, 0], true, 1⟩,
      ⟨(.inl .r3c, false), [1, 2], true, 2⟩, ⟨(.inl .r2b, false), [1, 2, 3], true, 3⟩, ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .k22, false), [0, 1, 2, 3], true, 5⟩,
      ⟨(.inr .ksym2, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r3b, false), [0, 1, 2], true, 5⟩, ⟨(.inl .r3b, true), [1, 2, 3], true, 6⟩, ⟨(.inl .r2b, false), [1, 3, 0], true, 7⟩,
      ⟨(.inl .r3c, true), [1, 3], false, 8⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 9⟩, ⟨(.inl .r2d, false), [2, 3], false, 8⟩, ⟨(.inl .r3c, false), [1, 3], true, 10⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 11⟩, ⟨(.inl .r2d, false), [1, 3], false, 9⟩, ⟨(.inl .r2d, false), [1, 2], false, 8⟩, ⟨(.inl .r2b, false), [2, 3, 0], true, 6⟩,
      ⟨(.inl .r2b, false), [2, 3, 1], true, 7⟩, ⟨(.inl .r3c, true), [2, 3], false, 8⟩, ⟨(.inl .r3c, false), [2, 3], true, 9⟩, ⟨(.inl .r1a, false), [2, 3], true, 10⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 8⟩, ⟨(.inl .r2d, false), [1, 2], true, 7⟩, ⟨(.inl .r2d, false), [1, 3], true, 8⟩, ⟨(.inl .r2d, false), [2, 3], true, 7⟩,
      ⟨(.inl .r3c, false), [1, 3], false, 9⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 8⟩, ⟨(.inl .r3c, true), [1, 3], true, 7⟩, ⟨(.inl .r2b, false), [1, 3, 0], false, 6⟩,
      ⟨(.inl .r2d, false), [1, 2], true, 8⟩, ⟨(.inl .r2d, false), [1, 3], true, 9⟩, ⟨(.inl .r1b, false), [1], true, 10⟩, ⟨(.inl .r2d, false), [2, 3], false, 9⟩,
      ⟨(.inl .r1b, false), [2], true, 8⟩, ⟨(.inl .r2d, false), [0, 3], false, 8⟩, ⟨(.inl .r1b, false), [0], true, 7⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], true, 5⟩,
      ⟨(.inl .r2b, false), [0, 2, 3], true, 6⟩, ⟨(.inl .r1a, false), [0, 2], true, 7⟩, ⟨(.inl .r3c, true), [1, 3], true, 6⟩, ⟨(.inl .r1a, false), [1, 3], true, 5⟩,
      ⟨(.inl .r2d, false), [0, 1], false, 5⟩, ⟨(.inl .r1b, false), [1], true, 6⟩]
  | true, false, true, true, false, true, true, true =>
    [⟨(.inl .r1b, false), [0], false, 1⟩, ⟨(.inl .r2d, false), [1, 2], true, 3⟩, ⟨(.inl .r2d, false), [1, 3], true, 4⟩, ⟨(.inl .r2d, false), [0, 2], true, 2⟩,
      ⟨(.inl .r2d, false), [0, 3], true, 3⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inr .k11, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], false, 4⟩,
      ⟨(.inl .r1a, false), [0, 2], true, 3⟩, ⟨(.inl .r1a, false), [1, 3], true, 3⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1b, false), [1], false, 2⟩,
      ⟨(.inl .r2d, false), [0, 1], true, 1⟩, ⟨(.inl .r1a, false), [0, 2], false, 2⟩, ⟨(.inl .r2b, false), [0, 2, 1], false, 1⟩, ⟨(.inl .r3b, true), [0, 1, 2], false, 0⟩,
      ⟨(.inl .r1b, false), [3], false, 3⟩, ⟨(.inl .r1b, false), [0], false, 4⟩, ⟨(.inl .r2d, false), [0, 3], false, 3⟩, ⟨(.inl .r2d, false), [0, 1], false, 2⟩,
      ⟨(.inl .r2d, false), [1, 3], true, 3⟩, ⟨(.inl .r1a, false), [1, 3], false, 5⟩, ⟨(.inl .r3c, false), [1, 3], false, 4⟩, ⟨(.inl .r3c, true), [1, 3], true, 3⟩,
      ⟨(.inl .r2b, false), [1, 3, 0], false, 2⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 1⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 1⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 10⟩,
      ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 9⟩, ⟨(.inr .k32, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .ksym6, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inl .r3b, true), [0, 2, 3], false, 7⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], true, 8⟩, ⟨(.inl .r2b, false), [2, 3, 0], true, 9⟩, ⟨(.inl .r2b, false), [2, 3, 1], true, 10⟩, ⟨(.inl .r3c, true), [2, 3], false, 11⟩,
      ⟨(.inl .r3c, false), [2, 3], true, 12⟩, ⟨(.inl .r1a, false), [2, 3], true, 13⟩, ⟨(.inl .r2d, false), [2, 3], false, 11⟩, ⟨(.inl .r2d, false), [2, 3], false, 12⟩,
      ⟨(.inl .r1b, false), [2], true, 11⟩, ⟨(.inl .r1b, false), [3], true, 11⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], true, 7⟩, ⟨(.inl .r3c, true), [0, 2], false, 8⟩,
      ⟨(.inl .r2b, false), [0, 2, 1], true, 9⟩, ⟨(.inl .r2d, false), [1, 2], false, 8⟩, ⟨(.inl .r1a, false), [0, 2], true, 10⟩, ⟨(.inl .r3c, true), [1, 3], false, 7⟩,
      ⟨(.inl .r2b, false), [1, 3, 2], true, 8⟩, ⟨(.inl .r2d, false), [2, 3], false, 7⟩, ⟨(.inl .r1a, false), [1, 3], true, 9⟩, ⟨(.inl .r2d, false), [0, 3], false, 8⟩,
      ⟨(.inl .r2d, false), [0, 2], false, 7⟩, ⟨(.inl .r2d, false), [1, 3], false, 9⟩, ⟨(.inl .r2d, false), [1, 2], false, 8⟩, ⟨(.inl .r2d, false), [2, 3], false, 10⟩,
      ⟨(.inl .r1b, false), [2], true, 9⟩, ⟨(.inl .r1b, false), [3], true, 9⟩, ⟨(.inl .r2d, false), [0, 1], false, 8⟩, ⟨(.inl .r1b, false), [0], true, 7⟩,
      ⟨(.inl .r2d, false), [0, 1], false, 7⟩, ⟨(.inl .r1b, false), [1], true, 8⟩]
  | true, false, true, true, true, false, false, false =>
    [⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 2], false, 2⟩, ⟨(.inl .r3c, false), [0, 2], false, 1⟩, ⟨(.inl .r3b, true), [0, 1, 2], false, 0⟩,
      ⟨(.inl .r1a, false), [1, 3], false, 3⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 2⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 1⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 1⟩,
      ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inr .ksym6, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r1a, false), [2, 3], true, 5⟩, ⟨(.inl .r2d, false), [0, 3], false, 6⟩,
      ⟨(.inl .r2d, false), [0, 2], false, 5⟩]
  | true, false, true, true, true, false, true, true =>
    [⟨(.inr .k11, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1b, false), [1], false, 2⟩, ⟨(.inl .r2d, false), [0, 1], true, 1⟩,
      ⟨(.inl .r1a, false), [0, 3], false, 2⟩, ⟨(.inl .r2b, false), [0, 3, 1], false, 1⟩, ⟨(.inl .r2a, false), [0, 3, 1, 2], false, 0⟩, ⟨(.inl .r3c, true), [1, 2], false, 1⟩,
      ⟨(.inr .k12, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 3⟩, ⟨(.inr .ksym2, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 3⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], true, 3⟩, ⟨(.inl .r1a, false), [2, 3], true, 4⟩, ⟨(.inl .r1a, false), [1, 3], true, 3⟩, ⟨(.inl .r2d, false), [1, 2], true, 3⟩,
      ⟨(.inl .r2b, false), [0, 2, 1], false, 4⟩, ⟨(.inl .r3c, true), [0, 2], true, 3⟩, ⟨(.inl .r3c, false), [1, 3], false, 5⟩, ⟨(.inl .r2b, false), [1, 3, 0], false, 4⟩,
      ⟨(.inl .r2d, false), [0, 3], false, 6⟩, ⟨(.inl .r1b, false), [0], true, 5⟩, ⟨(.inl .r2d, false), [1, 3], false, 5⟩, ⟨(.inl .r2d, false), [2, 3], false, 6⟩,
      ⟨(.inl .r1b, false), [3], true, 7⟩, ⟨(.inl .r2d, false), [0, 2], false, 6⟩, ⟨(.inl .r2d, false), [0, 1], false, 5⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], true, 3⟩,
      ⟨(.inl .r3c, true), [0, 2], false, 4⟩, ⟨(.inl .r2b, false), [0, 2, 1], true, 5⟩, ⟨(.inl .r2d, false), [1, 2], false, 4⟩, ⟨(.inl .r3c, false), [0, 2], true, 6⟩,
      ⟨(.inl .r2d, false), [0, 2], false, 5⟩, ⟨(.inl .r1a, false), [0, 2], true, 7⟩, ⟨(.inl .r2d, false), [0, 1], false, 4⟩, ⟨(.inl .r2b, false), [1, 3, 0], true, 3⟩,
      ⟨(.inl .r3c, true), [1, 3], false, 4⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 5⟩, ⟨(.inl .r2d, false), [2, 3], false, 4⟩, ⟨(.inl .r1a, false), [1, 3], true, 6⟩]
  | true, false, true, true, true, true, false, true =>
    [⟨(.inr .k21, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1b, false), [2], false, 2⟩, ⟨(.inl .r2d, false), [0, 2], true, 1⟩,
      ⟨(.inr .k22, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inl .r2d, false), [0, 1], true, 5⟩, ⟨(.inl .r2d, false), [0, 2], true, 6⟩, ⟨(.inl .r2d, false), [0, 3], true, 7⟩,
      ⟨(.inl .r1b, false), [0], true, 8⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 3⟩, ⟨(.inl .r3c, false), [0, 1], true, 4⟩, ⟨(.inl .r2b, false), [0, 1, 2], true, 5⟩,
      ⟨(.inl .r2b, false), [0, 1, 3], true, 6⟩, ⟨(.inl .r1a, false), [0, 1], true, 7⟩, ⟨(.inl .r2b, false), [2, 3, 0], true, 3⟩, ⟨(.inl .r3c, true), [2, 3], false, 4⟩,
      ⟨(.inl .r3c, false), [2, 3], true, 5⟩, ⟨(.inl .r2d, false), [2, 3], false, 4⟩, ⟨(.inl .r1a, false), [2, 3], true, 6⟩]
  | true, false, true, true, true, true, true, false =>
    [⟨(.inr .k31, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 2⟩, ⟨(.inl .r3c, false), [0, 1], false, 1⟩,
      ⟨(.inl .r3b, false), [0, 1, 2], true, 0⟩, ⟨(.inl .r1b, false), [3], false, 3⟩, ⟨(.inl .r2d, false), [1, 3], true, 2⟩, ⟨(.inl .r1a, false), [2, 3], false, 2⟩,
      ⟨(.inl .r3c, false), [2, 3], true, 3⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .k21, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 4⟩,
      ⟨(.inl .r3b, false), [0, 1, 3], true, 5⟩, ⟨(.inl .r3b, false), [1, 2, 3], false, 6⟩, ⟨(.inl .r3a, false), [1, 2, 3], false, 6⟩, ⟨(.inl .r1a, false), [1, 3], true, 7⟩,
      ⟨(.inl .r2d, false), [0, 3], false, 8⟩, ⟨(.inl .r2d, false), [0, 1], false, 7⟩, ⟨(.inl .r2a, false), [0, 3, 1, 2], true, 5⟩, ⟨(.inl .r3c, true), [0, 3], false, 6⟩,
      ⟨(.inl .r2b, false), [0, 3, 1], true, 7⟩, ⟨(.inl .r2d, false), [1, 3], false, 6⟩, ⟨(.inl .r3c, false), [0, 3], true, 8⟩, ⟨(.inl .r2d, false), [0, 3], false, 7⟩,
      ⟨(.inl .r1a, false), [0, 3], true, 9⟩, ⟨(.inl .r2d, false), [0, 1], false, 6⟩, ⟨(.inl .r2b, false), [1, 2, 0], true, 5⟩, ⟨(.inl .r3c, true), [1, 2], false, 6⟩,
      ⟨(.inl .r2b, false), [1, 2, 3], true, 7⟩, ⟨(.inl .r1a, false), [1, 2], true, 8⟩]
  | true, true, false, true, false, false, false, true =>
    [⟨(.inl .r1b, false), [0], false, 1⟩, ⟨(.inr .k32, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 2], false, 2⟩,
      ⟨(.inl .r3c, false), [0, 2], false, 1⟩, ⟨(.inl .r3b, true), [0, 1, 2], false, 0⟩, ⟨(.inl .r1b, false), [1], false, 2⟩, ⟨(.inl .r2d, false), [1, 2], true, 3⟩,
      ⟨(.inl .r1b, false), [0], false, 4⟩, ⟨(.inl .r2d, false), [0, 2], false, 3⟩, ⟨(.inl .r2d, false), [0, 1], false, 2⟩, ⟨(.inl .r2d, false), [1, 2], true, 3⟩,
      ⟨(.inl .r1a, false), [1, 3], false, 5⟩, ⟨(.inl .r3c, false), [1, 3], false, 4⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 3⟩, ⟨(.inl .r2b, false), [1, 3, 0], false, 2⟩,
      ⟨(.inl .r3a, false), [1, 2, 3], true, 1⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 1⟩, ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 9⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 7⟩,
      ⟨(.inr .ksym6, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inl .r3b, false), [0, 2, 3], true, 7⟩, ⟨(.inl .r3b, true), [1, 2, 3], false, 8⟩, ⟨(.inl .r2b, false), [2, 3, 0], true, 9⟩,
      ⟨(.inl .r2b, false), [2, 3, 1], true, 10⟩, ⟨(.inl .r3c, true), [2, 3], false, 11⟩, ⟨(.inl .r3c, false), [2, 3], true, 12⟩, ⟨(.inl .r1a, false), [2, 3], true, 13⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 11⟩, ⟨(.inl .r2d, false), [2, 3], false, 12⟩, ⟨(.inl .r1b, false), [2], true, 11⟩, ⟨(.inl .r1b, false), [3], true, 11⟩,
      ⟨(.inl .r2d, false), [0, 1], false, 10⟩, ⟨(.inl .r1b, false), [0], true, 9⟩, ⟨(.inl .r2a, false), [0, 3, 1, 2], true, 7⟩, ⟨(.inl .r2b, false), [0, 3, 1], true, 8⟩,
      ⟨(.inl .r1a, false), [0, 3], true, 9⟩, ⟨(.inl .r3c, false), [1, 2], false, 8⟩, ⟨(.inl .r1a, false), [1, 2], true, 7⟩, ⟨(.inl .r2d, false), [0, 2], false, 7⟩,
      ⟨(.inl .r2d, false), [1, 2], false, 8⟩, ⟨(.inl .r1b, false), [2], true, 9⟩]
  | true, true, false, true, false, false, true, false =>
    [⟨(.inl .r1b, false), [0], false, 1⟩, ⟨(.inr .k22, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 3], false, 2⟩,
      ⟨(.inl .r3c, false), [0, 3], false, 1⟩, ⟨(.inl .r2a, false), [0, 3, 1, 2], false, 0⟩, ⟨(.inl .r1b, false), [1], false, 2⟩, ⟨(.inl .r2d, false), [1, 3], true, 3⟩,
      ⟨(.inl .r1b, false), [0], false, 4⟩, ⟨(.inl .r2d, false), [0, 3], false, 3⟩, ⟨(.inl .r2d, false), [0, 1], false, 2⟩, ⟨(.inl .r2b, false), [1, 2, 0], true, 1⟩,
      ⟨(.inl .r3c, true), [1, 2], false, 2⟩, ⟨(.inl .r2b, false), [1, 2, 3], true, 3⟩, ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 5⟩,
      ⟨(.inr .ksym2, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r3b, true), [0, 1, 2], false, 5⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 6⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 6⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], false, 6⟩, ⟨(.inl .r3a, false), [1, 2, 3], false, 6⟩, ⟨(.inl .r2b, false), [1, 3, 0], true, 7⟩, ⟨(.inl .r3c, true), [1, 3], false, 8⟩,
      ⟨(.inl .r2b, false), [1, 3, 2], true, 9⟩, ⟨(.inl .r2d, false), [2, 3], false, 8⟩, ⟨(.inl .r3c, false), [1, 3], true, 10⟩, ⟨(.inl .r1a, false), [1, 3], true, 11⟩,
      ⟨(.inl .r2d, false), [1, 3], false, 9⟩, ⟨(.inl .r2d, false), [1, 2], false, 8⟩, ⟨(.inl .r2d, false), [2, 3], true, 9⟩, ⟨(.inl .r3c, false), [2, 3], false, 10⟩,
      ⟨(.inl .r3c, true), [2, 3], true, 9⟩, ⟨(.inl .r2b, false), [2, 3, 1], false, 8⟩, ⟨(.inl .r2b, false), [2, 3, 0], false, 7⟩, ⟨(.inl .r3b, true), [1, 2, 3], true, 6⟩,
      ⟨(.inl .r2b, false), [1, 3, 0], true, 7⟩, ⟨(.inl .r3c, true), [1, 3], false, 8⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 9⟩, ⟨(.inl .r2d, false), [2, 3], false, 8⟩,
      ⟨(.inl .r3c, false), [1, 3], true, 10⟩, ⟨(.inl .r1a, false), [1, 3], true, 11⟩, ⟨(.inl .r2d, false), [1, 3], false, 9⟩, ⟨(.inl .r2d, false), [1, 2], false, 8⟩,
      ⟨(.inl .r2d, false), [1, 2], true, 8⟩, ⟨(.inl .r2d, false), [1, 3], true, 9⟩, ⟨(.inl .r1b, false), [1], true, 10⟩, ⟨(.inl .r2d, false), [2, 3], false, 9⟩,
      ⟨(.inl .r1b, false), [2], true, 8⟩, ⟨(.inl .r2d, false), [0, 3], false, 8⟩, ⟨(.inl .r1b, false), [0], true, 7⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 5⟩,
      ⟨(.inl .r2b, false), [0, 1, 3], true, 6⟩, ⟨(.inl .r1a, false), [0, 1], true, 7⟩, ⟨(.inl .r3c, true), [2, 3], true, 6⟩, ⟨(.inl .r1a, false), [2, 3], true, 5⟩,
      ⟨(.inl .r2d, false), [0, 2], false, 5⟩, ⟨(.inl .r2d, false), [1, 2], false, 6⟩, ⟨(.inl .r1b, false), [2], true, 7⟩]
  | true, true, false, true, false, true, false, false =>
    [⟨(.inl .r1b, false), [0], false, 1⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1b, false), [3], false, 2⟩,
      ⟨(.inl .r1b, false), [2], false, 2⟩, ⟨(.inl .r2d, false), [2, 3], true, 3⟩, ⟨(.inr .k11, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], true, 5⟩,
      ⟨(.inl .r3c, true), [0, 2], false, 6⟩, ⟨(.inl .r1a, false), [0, 2], true, 7⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 6⟩, ⟨(.inl .r1a, false), [1, 3], true, 5⟩,
      ⟨(.inl .r2d, false), [0, 2], false, 5⟩, ⟨(.inl .r2d, false), [1, 2], false, 6⟩, ⟨(.inl .r1b, false), [2], true, 7⟩]
  | true, true, false, true, false, true, true, true =>
    [⟨(.inl .r1b, false), [0], false, 1⟩, ⟨(.inl .r2d, false), [1, 2], true, 3⟩, ⟨(.inl .r2d, false), [1, 3], true, 4⟩, ⟨(.inl .r2d, false), [0, 2], true, 2⟩,
      ⟨(.inl .r2d, false), [0, 3], true, 3⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inr .k11, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], false, 4⟩,
      ⟨(.inl .r1a, false), [0, 2], true, 3⟩, ⟨(.inl .r1a, false), [1, 3], true, 3⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 2⟩,
      ⟨(.inl .r3c, false), [0, 1], false, 1⟩, ⟨(.inl .r3b, false), [0, 1, 2], true, 0⟩, ⟨(.inl .r1b, false), [0], false, 2⟩, ⟨(.inl .r1a, false), [2, 3], false, 2⟩,
      ⟨(.inl .r2b, false), [2, 3, 0], true, 3⟩, ⟨(.inl .r1b, false), [3], false, 4⟩, ⟨(.inl .r1b, false), [2], false, 4⟩, ⟨(.inl .r2d, false), [2, 3], true, 5⟩,
      ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 11⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 9⟩, ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 8⟩, ⟨(.inr .k11, false), [0, 1, 2, 3], true, 6⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 8⟩, ⟨(.inl .r1a, false), [0, 2], true, 7⟩, ⟨(.inl .r2b, false), [1, 3, 0], true, 7⟩, ⟨(.inl .r3c, true), [1, 3], false, 8⟩,
      ⟨(.inl .r2b, false), [1, 3, 2], true, 9⟩, ⟨(.inl .r2d, false), [2, 3], false, 8⟩, ⟨(.inl .r3c, false), [1, 3], true, 10⟩, ⟨(.inl .r2d, false), [1, 3], false, 9⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 11⟩, ⟨(.inl .r2d, false), [1, 2], false, 8⟩, ⟨(.inl .r2d, false), [1, 2], true, 8⟩, ⟨(.inl .r2d, false), [1, 3], true, 9⟩,
      ⟨(.inl .r1b, false), [1], true, 10⟩, ⟨(.inl .r1b, false), [3], true, 9⟩, ⟨(.inl .r2d, false), [0, 2], false, 8⟩, ⟨(.inl .r1b, false), [0], true, 7⟩,
      ⟨(.inl .r2d, false), [0, 2], false, 7⟩, ⟨(.inl .r2d, false), [1, 2], false, 8⟩, ⟨(.inl .r1b, false), [2], true, 9⟩]
  | true, true, false, true, true, false, false, false =>
    [⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 2⟩, ⟨(.inl .r3c, false), [0, 1], false, 1⟩, ⟨(.inl .r3b, false), [0, 1, 2], true, 0⟩,
      ⟨(.inl .r1a, false), [2, 3], false, 2⟩, ⟨(.inl .r2b, false), [2, 3, 1], true, 3⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 4⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 5⟩, ⟨(.inl .r2d, false), [0, 3], false, 6⟩, ⟨(.inl .r2d, false), [0, 1], false, 5⟩]
  | true, true, false, true, true, false, true, true =>
    [⟨(.inr .k11, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1b, false), [1], false, 2⟩, ⟨(.inl .r2d, false), [0, 1], true, 1⟩,
      ⟨(.inr .k12, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inl .r2d, false), [0, 1], true, 5⟩, ⟨(.inl .r2d, false), [0, 2], true, 6⟩, ⟨(.inl .r2d, false), [0, 3], true, 7⟩,
      ⟨(.inl .r1b, false), [0], true, 8⟩, ⟨(.inl .r2b, false), [0, 2, 3], false, 7⟩, ⟨(.inl .r3c, true), [0, 2], true, 6⟩, ⟨(.inl .r2b, false), [0, 2, 1], false, 5⟩,
      ⟨(.inl .r2a, false), [0, 2, 1, 3], false, 4⟩, ⟨(.inl .r1a, false), [0, 2], true, 3⟩, ⟨(.inl .r2d, false), [0, 1], false, 4⟩, ⟨(.inl .r2b, false), [1, 3, 0], true, 3⟩,
      ⟨(.inl .r3c, true), [1, 3], false, 4⟩, ⟨(.inl .r3c, false), [1, 3], true, 5⟩, ⟨(.inl .r2d, false), [1, 3], false, 4⟩, ⟨(.inl .r1a, false), [1, 3], true, 6⟩]
  | true, true, false, true, true, true, false, true =>
    [⟨(.inr .k21, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1b, false), [2], false, 2⟩, ⟨(.inl .r2d, false), [0, 2], true, 1⟩,
      ⟨(.inl .r1a, false), [0, 3], false, 2⟩, ⟨(.inl .r2b, false), [0, 3, 2], false, 1⟩, ⟨(.inl .r2a, false), [0, 3, 1, 2], false, 0⟩, ⟨(.inl .r3c, false), [1, 2], true, 1⟩,
      ⟨(.inr .k22, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 3⟩, ⟨(.inr .ksym2, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 3⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], true, 3⟩, ⟨(.inl .r1a, false), [2, 3], true, 4⟩, ⟨(.inl .r1a, false), [1, 3], true, 3⟩, ⟨(.inl .r2b, false), [0, 1, 2], false, 4⟩,
      ⟨(.inl .r3c, true), [0, 1], true, 3⟩, ⟨(.inl .r3c, false), [2, 3], false, 5⟩, ⟨(.inl .r2b, false), [2, 3, 0], false, 4⟩, ⟨(.inl .r2d, false), [0, 3], false, 6⟩,
      ⟨(.inl .r1b, false), [0], true, 5⟩, ⟨(.inl .r2d, false), [1, 3], false, 5⟩, ⟨(.inl .r2d, false), [2, 3], false, 6⟩, ⟨(.inl .r1b, false), [3], true, 7⟩,
      ⟨(.inl .r2d, false), [0, 2], false, 6⟩, ⟨(.inl .r2d, false), [0, 1], false, 5⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 3⟩, ⟨(.inl .r3c, true), [0, 1], false, 4⟩,
      ⟨(.inl .r3c, false), [0, 1], true, 5⟩, ⟨(.inl .r2d, false), [0, 1], false, 4⟩, ⟨(.inl .r2b, false), [0, 1, 2], false, 7⟩, ⟨(.inl .r1a, false), [0, 1], true, 6⟩,
      ⟨(.inl .r2b, false), [2, 3, 0], true, 3⟩, ⟨(.inl .r2b, false), [2, 3, 1], true, 4⟩, ⟨(.inl .r3c, true), [2, 3], false, 5⟩, ⟨(.inl .r1a, false), [2, 3], true, 6⟩]
  | true, true, false, true, true, true, true, false =>
    [⟨(.inr .k31, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 2], false, 2⟩, ⟨(.inl .r3c, false), [0, 2], false, 1⟩,
      ⟨(.inl .r3b, true), [0, 1, 2], false, 0⟩, ⟨(.inl .r1a, false), [1, 3], false, 3⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 2⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 1⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], true, 1⟩, ⟨(.inl .r1b, false), [1], false, 3⟩, ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .ksym6, false), [0, 1, 2, 3], true, 6⟩,
      ⟨(.inr .k31, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r1a, false), [2, 3], true, 7⟩, ⟨(.inl .r2d, false), [0, 3], false, 8⟩, ⟨(.inl .r2d, false), [0, 2], false, 7⟩,
      ⟨(.inl .r2a, false), [0, 3, 1, 2], true, 5⟩, ⟨(.inl .r3c, true), [0, 3], false, 6⟩, ⟨(.inl .r2b, false), [0, 3, 2], true, 7⟩, ⟨(.inl .r2d, false), [2, 3], false, 6⟩,
      ⟨(.inl .r3c, false), [0, 3], true, 8⟩, ⟨(.inl .r2d, false), [0, 3], false, 7⟩, ⟨(.inl .r1a, false), [0, 3], true, 9⟩, ⟨(.inl .r2d, false), [0, 2], false, 6⟩,
      ⟨(.inl .r2b, false), [1, 2, 0], true, 5⟩, ⟨(.inl .r3c, false), [1, 2], true, 6⟩, ⟨(.inl .r2b, false), [1, 2, 3], true, 7⟩, ⟨(.inl .r1a, false), [1, 2], true, 8⟩]
  | true, true, true, false, false, false, false, true =>
    [⟨(.inl .r1b, false), [0], false, 1⟩, ⟨(.inr .k32, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1b, false), [2], false, 2⟩,
      ⟨(.inl .r1b, false), [1], false, 2⟩, ⟨(.inl .r2d, false), [1, 2], true, 3⟩, ⟨(.inr .k31, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r2a, false), [0, 3, 1, 2], true, 5⟩,
      ⟨(.inl .r3c, true), [0, 3], false, 6⟩, ⟨(.inl .r1a, false), [0, 3], true, 7⟩, ⟨(.inl .r2b, false), [1, 2, 3], false, 6⟩, ⟨(.inl .r1a, false), [1, 2], true, 5⟩,
      ⟨(.inl .r2d, false), [0, 3], false, 5⟩, ⟨(.inl .r2d, false), [1, 3], false, 6⟩, ⟨(.inl .r2d, false), [2, 3], false, 7⟩, ⟨(.inl .r1b, false), [3], true, 8⟩]
  | true, true, true, false, false, false, true, false =>
    [⟨(.inl .r1b, false), [0], false, 1⟩, ⟨(.inr .k22, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 2⟩,
      ⟨(.inl .r3c, false), [0, 1], false, 1⟩, ⟨(.inl .r3b, false), [0, 1, 2], true, 0⟩, ⟨(.inl .r1b, false), [3], false, 3⟩, ⟨(.inl .r1b, false), [0], false, 4⟩,
      ⟨(.inl .r2d, false), [0, 3], false, 3⟩, ⟨(.inl .r2d, false), [0, 1], false, 2⟩, ⟨(.inl .r1a, false), [2, 3], false, 5⟩, ⟨(.inl .r3c, true), [2, 3], true, 4⟩,
      ⟨(.inl .r2b, false), [2, 3, 1], false, 3⟩, ⟨(.inl .r2b, false), [2, 3, 0], false, 2⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 9⟩, ⟨(.inr .k32, false), [0, 1, 2, 3], true, 7⟩,
      ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inl .r3b, true), [0, 1, 3], false, 7⟩, ⟨(.inl .r3a, true), [1, 2, 3], true, 8⟩, ⟨(.inl .r3b, true), [1, 2, 3], true, 8⟩,
      ⟨(.inl .r2b, false), [1, 3, 0], true, 9⟩, ⟨(.inl .r3c, true), [1, 3], false, 10⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 11⟩, ⟨(.inl .r2d, false), [2, 3], false, 10⟩,
      ⟨(.inl .r3c, false), [1, 3], true, 12⟩, ⟨(.inl .r1a, false), [1, 3], true, 13⟩, ⟨(.inl .r2d, false), [1, 3], false, 11⟩, ⟨(.inl .r2d, false), [1, 2], false, 10⟩,
      ⟨(.inl .r2d, false), [1, 2], true, 10⟩, ⟨(.inl .r2d, false), [1, 3], true, 11⟩, ⟨(.inl .r1b, false), [1], true, 12⟩, ⟨(.inl .r1b, false), [3], true, 11⟩,
      ⟨(.inl .r2d, false), [0, 2], false, 10⟩, ⟨(.inl .r1b, false), [0], true, 9⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inl .r2b, false), [0, 1, 2], true, 8⟩,
      ⟨(.inl .r1a, false), [0, 1], true, 9⟩, ⟨(.inl .r3c, false), [2, 3], false, 8⟩, ⟨(.inl .r1a, false), [2, 3], true, 7⟩, ⟨(.inl .r2d, false), [0, 3], false, 7⟩,
      ⟨(.inl .r2d, false), [1, 3], false, 8⟩, ⟨(.inl .r2d, false), [2, 3], false, 9⟩, ⟨(.inl .r1b, false), [3], true, 10⟩]
  | true, true, true, false, false, true, false, false =>
    [⟨(.inl .r1b, false), [0], false, 1⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 2], false, 2⟩,
      ⟨(.inl .r3c, false), [0, 2], false, 1⟩, ⟨(.inl .r3b, true), [0, 1, 2], false, 0⟩, ⟨(.inl .r1b, false), [3], false, 3⟩, ⟨(.inl .r1b, false), [0], false, 4⟩,
      ⟨(.inl .r2d, false), [0, 3], false, 3⟩, ⟨(.inl .r2d, false), [0, 2], false, 2⟩, ⟨(.inl .r2d, false), [2, 3], true, 3⟩, ⟨(.inl .r1a, false), [1, 3], false, 5⟩,
      ⟨(.inl .r2b, false), [1, 3, 2], false, 4⟩, ⟨(.inl .r3c, true), [1, 3], true, 3⟩, ⟨(.inl .r2b, false), [1, 3, 0], false, 2⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 1⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], true, 1⟩, ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 9⟩, ⟨(.inr .k32, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .ksym6, false), [0, 1, 2, 3], true, 6⟩,
      ⟨(.inl .r3b, true), [0, 2, 3], false, 7⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 8⟩, ⟨(.inl .r2b, false), [2, 3, 0], true, 9⟩, ⟨(.inl .r2b, false), [2, 3, 1], true, 10⟩,
      ⟨(.inl .r3c, true), [2, 3], false, 11⟩, ⟨(.inl .r3c, false), [2, 3], true, 12⟩, ⟨(.inl .r1a, false), [2, 3], true, 13⟩, ⟨(.inl .r2d, false), [2, 3], false, 11⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 12⟩, ⟨(.inl .r1b, false), [2], true, 11⟩, ⟨(.inl .r1b, false), [3], true, 11⟩, ⟨(.inl .r2d, false), [0, 1], false, 10⟩,
      ⟨(.inl .r1b, false), [0], true, 9⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], true, 7⟩, ⟨(.inl .r2b, false), [0, 2, 1], true, 8⟩, ⟨(.inl .r1a, false), [0, 2], true, 9⟩,
      ⟨(.inl .r3c, false), [1, 3], false, 8⟩, ⟨(.inl .r1a, false), [1, 3], true, 7⟩, ⟨(.inl .r2d, false), [0, 3], false, 7⟩, ⟨(.inl .r2d, false), [1, 3], false, 8⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 9⟩, ⟨(.inl .r1b, false), [3], true, 10⟩]
  | true, true, true, false, false, true, true, true =>
    [⟨(.inl .r1b, false), [0], false, 1⟩, ⟨(.inl .r2d, false), [1, 2], true, 3⟩, ⟨(.inl .r2d, false), [1, 3], true, 4⟩, ⟨(.inl .r2d, false), [0, 2], true, 2⟩,
      ⟨(.inl .r2d, false), [0, 3], true, 3⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inr .k11, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], false, 4⟩,
      ⟨(.inl .r1a, false), [0, 2], true, 3⟩, ⟨(.inl .r1a, false), [1, 3], true, 3⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1b, false), [1], false, 2⟩,
      ⟨(.inl .r2d, false), [0, 1], true, 1⟩, ⟨(.inl .r1a, false), [0, 3], false, 2⟩, ⟨(.inl .r2b, false), [0, 3, 1], false, 1⟩, ⟨(.inl .r2a, false), [0, 3, 1, 2], false, 0⟩,
      ⟨(.inl .r1b, false), [2], false, 3⟩, ⟨(.inl .r1b, false), [0], false, 4⟩, ⟨(.inl .r2d, false), [0, 2], false, 3⟩, ⟨(.inl .r2d, false), [0, 1], false, 2⟩,
      ⟨(.inl .r2b, false), [1, 2, 0], true, 1⟩, ⟨(.inl .r3c, true), [1, 2], false, 2⟩, ⟨(.inl .r3c, false), [1, 2], true, 3⟩, ⟨(.inl .r2d, false), [1, 2], false, 2⟩,
      ⟨(.inr .k12, false), [0, 1, 2, 3], true, 8⟩, ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .k22, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inr .ksym2, false), [0, 1, 2, 3], true, 4⟩,
      ⟨(.inl .r3b, false), [0, 1, 2], true, 5⟩, ⟨(.inl .r3b, true), [1, 2, 3], true, 6⟩, ⟨(.inl .r2b, false), [1, 3, 0], true, 7⟩, ⟨(.inl .r3c, true), [1, 3], false, 8⟩,
      ⟨(.inl .r2b, false), [1, 3, 2], true, 9⟩, ⟨(.inl .r2d, false), [2, 3], false, 8⟩, ⟨(.inl .r3c, false), [1, 3], true, 10⟩, ⟨(.inl .r1a, false), [1, 3], true, 11⟩,
      ⟨(.inl .r2d, false), [1, 3], false, 9⟩, ⟨(.inl .r2d, false), [1, 2], false, 8⟩, ⟨(.inl .r2b, false), [2, 3, 0], true, 6⟩, ⟨(.inl .r2b, false), [2, 3, 1], true, 7⟩,
      ⟨(.inl .r3c, true), [2, 3], false, 8⟩, ⟨(.inl .r3c, false), [2, 3], true, 9⟩, ⟨(.inl .r1a, false), [2, 3], true, 10⟩, ⟨(.inl .r2d, false), [2, 3], false, 8⟩,
      ⟨(.inl .r2d, false), [1, 2], true, 7⟩, ⟨(.inl .r2d, false), [1, 3], true, 8⟩, ⟨(.inl .r2d, false), [2, 3], true, 7⟩, ⟨(.inl .r3c, false), [1, 3], false, 9⟩,
      ⟨(.inl .r2b, false), [1, 3, 2], false, 8⟩, ⟨(.inl .r3c, true), [1, 3], true, 7⟩, ⟨(.inl .r2b, false), [1, 3, 0], false, 6⟩, ⟨(.inl .r2d, false), [1, 2], true, 8⟩,
      ⟨(.inl .r2d, false), [1, 3], true, 9⟩, ⟨(.inl .r1b, false), [1], true, 10⟩, ⟨(.inl .r2d, false), [2, 3], false, 9⟩, ⟨(.inl .r1b, false), [2], true, 8⟩,
      ⟨(.inl .r2a, false), [0, 2, 1, 3], true, 5⟩, ⟨(.inl .r3c, true), [0, 2], false, 6⟩, ⟨(.inl .r2b, false), [0, 2, 3], true, 7⟩, ⟨(.inl .r1a, false), [0, 2], true, 8⟩,
      ⟨(.inl .r2b, false), [1, 3, 2], true, 5⟩, ⟨(.inl .r3c, false), [1, 3], true, 6⟩, ⟨(.inl .r2d, false), [1, 2], false, 5⟩, ⟨(.inl .r1a, false), [1, 3], true, 7⟩,
      ⟨(.inl .r2d, false), [0, 2], false, 6⟩, ⟨(.inl .r2d, false), [0, 1], false, 5⟩, ⟨(.inl .r2d, false), [1, 2], false, 7⟩, ⟨(.inl .r1b, false), [1], true, 6⟩,
      ⟨(.inl .r1b, false), [2], true, 6⟩, ⟨(.inl .r2d, false), [0, 3], false, 6⟩, ⟨(.inl .r1b, false), [0], true, 5⟩, ⟨(.inl .r2d, false), [0, 3], false, 5⟩,
      ⟨(.inl .r2d, false), [1, 3], false, 6⟩, ⟨(.inl .r2d, false), [2, 3], false, 7⟩, ⟨(.inl .r1b, false), [3], true, 8⟩]
  | true, true, true, false, true, false, false, false =>
    [⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 3], false, 2⟩, ⟨(.inl .r3c, false), [0, 3], false, 1⟩, ⟨(.inl .r2a, false), [0, 3, 1, 2], false, 0⟩,
      ⟨(.inl .r2b, false), [1, 2, 3], true, 1⟩, ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 3⟩, ⟨(.inr .ksym2, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 3⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], true, 3⟩, ⟨(.inl .r1a, false), [2, 3], true, 4⟩, ⟨(.inl .r1a, false), [1, 3], true, 3⟩, ⟨(.inl .r2d, false), [0, 2], false, 4⟩,
      ⟨(.inl .r2d, false), [0, 1], false, 3⟩]
  | true, true, true, false, true, false, true, true =>
    [⟨(.inr .k11, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1b, false), [1], false, 2⟩, ⟨(.inl .r2d, false), [0, 1], true, 1⟩,
      ⟨(.inl .r1a, false), [0, 2], false, 2⟩, ⟨(.inl .r2b, false), [0, 2, 1], false, 1⟩, ⟨(.inl .r3b, true), [0, 1, 2], false, 0⟩, ⟨(.inl .r1a, false), [1, 3], false, 3⟩,
      ⟨(.inl .r3c, false), [1, 3], false, 2⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 1⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 1⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 6⟩,
      ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inr .ksym6, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r1a, false), [2, 3], true, 5⟩, ⟨(.inl .r2b, false), [0, 2, 3], false, 6⟩,
      ⟨(.inl .r3c, true), [0, 2], true, 5⟩, ⟨(.inl .r3c, true), [1, 3], true, 7⟩, ⟨(.inl .r2b, false), [1, 3, 0], false, 6⟩, ⟨(.inl .r2d, false), [0, 1], false, 8⟩,
      ⟨(.inl .r1b, false), [0], true, 7⟩, ⟨(.inl .r1b, false), [1], true, 7⟩, ⟨(.inl .r2d, false), [0, 3], false, 8⟩, ⟨(.inl .r2d, false), [0, 2], false, 7⟩,
      ⟨(.inl .r2a, false), [0, 2, 1, 3], true, 5⟩, ⟨(.inl .r3c, true), [0, 2], false, 6⟩, ⟨(.inl .r3c, false), [0, 2], true, 7⟩, ⟨(.inl .r2d, false), [0, 2], false, 6⟩,
      ⟨(.inl .r2b, false), [0, 2, 3], false, 9⟩, ⟨(.inl .r1a, false), [0, 2], true, 8⟩, ⟨(.inl .r2b, false), [1, 3, 0], true, 5⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 6⟩,
      ⟨(.inl .r3c, false), [1, 3], true, 7⟩, ⟨(.inl .r2d, false), [1, 2], false, 6⟩, ⟨(.inl .r1a, false), [1, 3], true, 8⟩]
  | true, true, true, false, true, true, false, true =>
    [⟨(.inr .k21, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 2⟩, ⟨(.inl .r3c, false), [0, 1], false, 1⟩,
      ⟨(.inl .r3b, false), [0, 1, 2], true, 0⟩, ⟨(.inl .r1b, false), [2], false, 3⟩, ⟨(.inl .r2d, false), [1, 2], true, 2⟩, ⟨(.inl .r1a, false), [2, 3], false, 2⟩,
      ⟨(.inl .r3c, true), [2, 3], false, 3⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .k31, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 4⟩,
      ⟨(.inl .r3b, true), [0, 1, 3], false, 5⟩, ⟨(.inl .r3a, true), [1, 2, 3], true, 6⟩, ⟨(.inl .r3b, true), [1, 2, 3], false, 7⟩, ⟨(.inl .r1a, false), [1, 2], true, 6⟩,
      ⟨(.inl .r2d, false), [0, 3], false, 8⟩, ⟨(.inl .r2d, false), [0, 1], false, 7⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r3c, true), [0, 1], false, 6⟩,
      ⟨(.inl .r3c, false), [0, 1], true, 7⟩, ⟨(.inl .r2d, false), [0, 1], false, 6⟩, ⟨(.inl .r2b, false), [0, 1, 3], false, 9⟩, ⟨(.inl .r1a, false), [0, 1], true, 8⟩,
      ⟨(.inl .r2b, false), [2, 3, 0], true, 5⟩, ⟨(.inl .r2b, false), [2, 3, 1], true, 6⟩, ⟨(.inl .r3c, false), [2, 3], true, 7⟩, ⟨(.inl .r1a, false), [2, 3], true, 8⟩]
  | true, true, true, false, true, true, true, false =>
    [⟨(.inr .k31, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inr .knk0, false), [0, 1, 2, 3], true, 0⟩, ⟨(.inl .r1b, false), [3], false, 2⟩, ⟨(.inl .r2d, false), [0, 3], true, 1⟩,
      ⟨(.inr .k32, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inl .r2d, false), [0, 1], true, 5⟩, ⟨(.inl .r2d, false), [0, 2], true, 6⟩, ⟨(.inl .r2d, false), [0, 3], true, 7⟩,
      ⟨(.inl .r1b, false), [0], true, 8⟩, ⟨(.inl .r2a, false), [0, 3, 1, 2], true, 3⟩, ⟨(.inl .r2b, false), [0, 3, 1], true, 4⟩, ⟨(.inl .r2b, false), [0, 3, 2], true, 5⟩,
      ⟨(.inl .r3c, false), [0, 3], true, 6⟩, ⟨(.inl .r2d, false), [0, 2], false, 5⟩, ⟨(.inl .r1a, false), [0, 3], true, 7⟩, ⟨(.inl .r2d, false), [0, 1], false, 4⟩,
      ⟨(.inl .r2b, false), [1, 2, 0], true, 3⟩, ⟨(.inl .r3c, true), [1, 2], false, 4⟩, ⟨(.inl .r3c, false), [1, 2], true, 5⟩, ⟨(.inl .r2d, false), [1, 2], false, 4⟩,
      ⟨(.inl .r1a, false), [1, 2], true, 6⟩]
  | _, _, _, _, _, _, _, _ => []

theorem chk325e : ∀ t0 t1 t2 t3 : Bool, (t0 ^^ t1 ^^ t2 ^^ t3) = false →
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
