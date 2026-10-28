/-
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

/-- `X` for `{a,b} = {0,1}`, `{α,β} = {0,2}`. -/
def X323_0102 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, false => [Gen.x 0 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 1]
  | false, false, true, true => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 0]
  | false, true, false, true => [Gen.x 0 1 (by decide), Gen.x 2 3 (by decide), Gen.neg 2]
  | false, true, true, false => [Gen.x 0 1 (by decide), Gen.x 2 3 (by decide), Gen.neg 0]
  | true, false, false, true => [Gen.x 0 1 (by decide), Gen.x 2 3 (by decide), Gen.neg 2]
  | true, false, true, false => [Gen.x 0 1 (by decide), Gen.x 2 3 (by decide), Gen.neg 0]
  | true, true, false, false => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 1]
  | true, true, true, true => [Gen.x 0 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 0]
  | _, _, _, _ => []

/-- `Y` for `{a,b} = {0,1}`, `{α,β} = {0,2}`. -/
def Y323_0102 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, false => [Gen.x 0 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 2]
  | false, false, true, true => [Gen.x 0 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 0, Gen.neg 2, Gen.neg 4]
  | false, true, false, true => [Gen.x 0 2 (by decide), Gen.x 1 3 (by decide), Gen.neg 3]
  | false, true, true, false => [Gen.x 0 2 (by decide), Gen.x 1 5 (by decide), Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.neg 1, Gen.neg 2, Gen.neg 5]
  | true, false, false, true => [Gen.x 0 2 (by decide), Gen.x 1 5 (by decide), Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.neg 1, Gen.neg 3, Gen.neg 5]
  | true, false, true, false => [Gen.x 0 2 (by decide), Gen.x 1 3 (by decide), Gen.neg 2]
  | true, true, false, false => [Gen.x 0 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 0, Gen.neg 3, Gen.neg 4]
  | true, true, true, true => [Gen.x 0 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 3]
  | _, _, _, _ => []

/-- The chains for `{a,b} = {0,1}`, `{α,β} = {0,2}`. -/
def S323_0102 : Bool → Bool → Bool → Bool → List (GStep ((Fam ⊕ MFam) × Bool) 6)
  | false, false, false, false =>
    [⟨(.inl .r1c, false), [0, 1, 4, 5], false, 2⟩, ⟨(.inl .r1b, false), [1], false, 0⟩, ⟨(.inl .r1a, false), [0, 2], false, 0⟩, ⟨(.inl .r2b, false), [0, 2, 1], true, 1⟩,
      ⟨(.inl .r1a, false), [2, 3], false, 1⟩, ⟨(.inl .r2b, false), [2, 3, 1], true, 2⟩, ⟨(.inl .r3a, true), [0, 2, 3], false, 0⟩, ⟨(.inl .r2b, false), [0, 2, 1], true, 1⟩,
      ⟨(.inl .r1a, false), [4, 5], false, 1⟩, ⟨(.inl .r2b, false), [4, 5, 1], true, 2⟩, ⟨(.inl .r2e, false), [1, 0, 2, 4, 5], true, 7⟩, ⟨(.inl .r4a, false), [0, 2, 4, 5], true, 6⟩,
      ⟨(.inl .r3e, false), [0, 2, 3, 4, 5], true, 5⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r4c, false), [2, 3, 4, 5], true, 3⟩, ⟨(.inl .r2a, false), [0, 2, 3, 5], false, 4⟩,
      ⟨(.inl .r3b, false), [2, 3, 5], true, 5⟩, ⟨(.inl .r3b, false), [2, 3, 5], false, 5⟩, ⟨(.inl .r3a, false), [2, 3, 5], false, 5⟩, ⟨(.inl .r1a, false), [2, 5], true, 6⟩,
      ⟨(.inl .r2d, false), [1, 5], false, 7⟩, ⟨(.inl .r2d, false), [1, 2], false, 6⟩, ⟨(.inl .r3a, true), [0, 2, 3], false, 4⟩, ⟨(.inl .r2b, false), [0, 2, 1], true, 5⟩,
      ⟨(.inl .r3c, false), [0, 2], true, 6⟩, ⟨(.inl .r2d, false), [0, 1], false, 5⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 8⟩, ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 7⟩,
      ⟨(.inr .k12, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r3b, false), [1, 2, 3], false, 5⟩, ⟨(.inl .r3a, false), [1, 2, 3], false, 5⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 6⟩, ⟨(.inl .r2d, false), [1, 2], true, 6⟩, ⟨(.inl .r2b, false), [0, 2, 1], false, 7⟩, ⟨(.inl .r3c, true), [0, 2], true, 6⟩,
      ⟨(.inl .r3b, true), [0, 1, 2], false, 5⟩, ⟨(.inl .r3c, false), [1, 3], false, 8⟩, ⟨(.inl .r2b, false), [1, 3, 0], false, 7⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 6⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], true, 6⟩, ⟨(.inl .r2d, false), [0, 3], false, 9⟩, ⟨(.inl .r1b, false), [0], true, 8⟩, ⟨(.inl .r2d, false), [1, 3], false, 8⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 9⟩, ⟨(.inl .r1b, false), [3], true, 10⟩, ⟨(.inl .r2b, false), [2, 3, 1], true, 7⟩, ⟨(.inl .r3c, true), [2, 3], false, 8⟩,
      ⟨(.inl .r1a, false), [2, 3], true, 9⟩, ⟨(.inl .r2d, false), [2, 3], false, 8⟩, ⟨(.inl .r1b, false), [3], true, 9⟩, ⟨(.inl .r2d, false), [2, 5], true, 8⟩,
      ⟨(.inl .r3c, true), [1, 3], false, 6⟩, ⟨(.inl .r2b, false), [1, 3, 5], true, 7⟩, ⟨(.inl .r2b, false), [0, 1, 3], true, 5⟩, ⟨(.inl .r2b, false), [0, 1, 5], true, 6⟩,
      ⟨(.inl .r2e, false), [2, 0, 1, 4, 5], true, 9⟩, ⟨(.inl .r3e, false), [0, 1, 3, 4, 5], true, 8⟩, ⟨(.inl .r3d, false), [0, 1, 3, 4, 5], true, 7⟩, ⟨(.inr .k21, false), [1, 3, 4, 5], true, 5⟩,
      ⟨(.inl .r2a, false), [0, 1, 4, 5], false, 7⟩, ⟨(.inl .r3b, false), [0, 1, 3], true, 6⟩, ⟨(.inl .r2a, false), [1, 3, 4, 5], false, 8⟩, ⟨(.inl .r1a, false), [1, 3], true, 7⟩,
      ⟨(.inl .r5a, false), [0, 1, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 3⟩]
  | false, false, true, true =>
    [⟨(.inl .r1b, false), [1], false, 2⟩, ⟨(.inl .r1b, false), [0], false, 2⟩, ⟨(.inl .r2d, false), [0, 1], true, 3⟩, ⟨(.inl .r2d, false), [0, 1], true, 2⟩,
      ⟨(.inl .r1c, false), [0, 1, 4, 5], false, 4⟩, ⟨(.inl .r1b, false), [1], false, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩, ⟨(.inl .r3c, false), [0, 1], true, 1⟩,
      ⟨(.inl .r1a, false), [1, 2], false, 1⟩, ⟨(.inl .r2b, false), [1, 2, 0], true, 2⟩, ⟨(.inl .r1a, false), [2, 3], false, 2⟩, ⟨(.inl .r2b, false), [2, 3, 0], true, 3⟩,
      ⟨(.inl .r3a, true), [1, 2, 3], false, 1⟩, ⟨(.inl .r2b, false), [1, 2, 0], true, 2⟩, ⟨(.inl .r1a, false), [4, 5], false, 2⟩, ⟨(.inl .r2b, false), [4, 5, 0], true, 3⟩,
      ⟨(.inl .r2e, false), [1, 0, 2, 4, 5], true, 9⟩, ⟨(.inl .r3d, false), [0, 1, 2, 4, 5], true, 8⟩, ⟨(.inl .r4a, false), [1, 2, 4, 5], true, 7⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 6⟩,
      ⟨(.inl .r3d, false), [1, 2, 3, 4, 5], true, 5⟩, ⟨(.inl .r4c, false), [2, 3, 4, 5], true, 4⟩, ⟨(.inl .r2a, false), [1, 2, 3, 5], false, 5⟩, ⟨(.inl .r3b, false), [2, 3, 5], true, 6⟩,
      ⟨(.inl .r3b, false), [2, 3, 5], false, 6⟩, ⟨(.inl .r3a, false), [2, 3, 5], false, 6⟩, ⟨(.inl .r1a, false), [2, 5], true, 7⟩, ⟨(.inl .r2b, false), [0, 1, 5], false, 8⟩,
      ⟨(.inl .r2b, false), [0, 1, 2], false, 7⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], false, 6⟩, ⟨(.inl .r3b, false), [0, 1, 2], true, 5⟩, ⟨(.inl .r2d, false), [1, 5], false, 9⟩,
      ⟨(.inl .r2d, false), [1, 2], false, 8⟩, ⟨(.inl .r3b, false), [0, 1, 2], false, 5⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inl .r3c, false), [0, 1], true, 7⟩,
      ⟨(.inl .r2b, false), [0, 1, 2], true, 8⟩, ⟨(.inl .r3a, true), [1, 2, 3], false, 5⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 10⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 9⟩,
      ⟨(.inr .k22, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .ksym2, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inr .ksym6, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 6⟩,
      ⟨(.inl .r2a, false), [0, 1, 2, 3], false, 7⟩, ⟨(.inl .r3b, false), [0, 1, 3], true, 6⟩, ⟨(.inl .r1a, false), [2, 3], true, 8⟩, ⟨(.inl .r2b, false), [1, 3, 0], true, 7⟩,
      ⟨(.inl .r3c, true), [1, 3], false, 8⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 9⟩, ⟨(.inl .r3c, false), [1, 3], true, 10⟩, ⟨(.inl .r1a, false), [1, 3], true, 11⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 8⟩, ⟨(.inl .r2d, false), [1, 3], false, 9⟩, ⟨(.inl .r2d, false), [1, 2], false, 8⟩, ⟨(.inl .r2d, false), [1, 2], true, 8⟩,
      ⟨(.inl .r2d, false), [1, 3], true, 9⟩, ⟨(.inl .r1b, false), [1], true, 10⟩, ⟨(.inl .r1b, false), [3], true, 9⟩, ⟨(.inl .r2d, false), [1, 5], false, 9⟩,
      ⟨(.inl .r2d, false), [1, 2], false, 8⟩, ⟨(.inl .r2d, false), [0, 1], true, 7⟩, ⟨(.inl .r2d, false), [0, 2], true, 8⟩, ⟨(.inl .r2d, false), [0, 5], true, 9⟩,
      ⟨(.inl .r1b, false), [0], true, 10⟩, ⟨(.inl .r2d, false), [2, 5], true, 8⟩, ⟨(.inl .r1a, false), [0, 1], false, 9⟩, ⟨(.inl .r2b, false), [0, 1, 5], false, 8⟩,
      ⟨(.inl .r3c, true), [0, 1], true, 7⟩, ⟨(.inl .r3a, true), [0, 1, 3], true, 6⟩, ⟨(.inl .r2e, false), [2, 0, 1, 4, 5], true, 11⟩, ⟨(.inl .r4a, false), [0, 1, 4, 5], true, 10⟩,
      ⟨(.inr .k32, false), [0, 1, 4, 5], true, 8⟩, ⟨(.inl .r3e, false), [0, 1, 3, 4, 5], true, 7⟩, ⟨(.inl .r3d, false), [0, 1, 3, 4, 5], true, 6⟩, ⟨(.inl .r3b, true), [0, 1, 3], true, 7⟩,
      ⟨(.inl .r3a, false), [0, 3, 5], true, 8⟩, ⟨(.inl .r3b, false), [0, 3, 5], true, 8⟩, ⟨(.inl .r2a, false), [0, 5, 1, 3], false, 7⟩, ⟨(.inl .r3b, true), [1, 3, 5], true, 8⟩,
      ⟨(.inl .r3a, true), [1, 4, 5], true, 9⟩, ⟨(.inl .r2a, false), [1, 4, 3, 5], false, 8⟩, ⟨(.inl .r3c, true), [1, 5], true, 14⟩, ⟨(.inl .r2b, false), [1, 5, 4], false, 13⟩,
      ⟨(.inl .r3c, false), [1, 5], false, 12⟩, ⟨(.inl .r2b, false), [1, 5, 0], false, 11⟩, ⟨(.inl .r3b, true), [1, 4, 5], false, 10⟩, ⟨(.inl .r2a, false), [1, 4, 3, 5], false, 9⟩,
      ⟨(.inl .r1a, false), [1, 4], true, 8⟩, ⟨(.inl .r2d, false), [4, 5], false, 11⟩, ⟨(.inl .r2d, false), [1, 5], false, 12⟩, ⟨(.inl .r2d, false), [1, 4], false, 11⟩,
      ⟨(.inl .r2d, false), [1, 4], true, 11⟩, ⟨(.inl .r2d, false), [1, 5], true, 12⟩, ⟨(.inl .r1b, false), [1], true, 13⟩, ⟨(.inl .r1b, false), [5], true, 12⟩,
      ⟨(.inl .r2d, false), [2, 4], false, 11⟩, ⟨(.inl .r5a, false), [0, 1, 2, 3, 4, 5], true, 5⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 4⟩]
  | false, true, false, true =>
    [⟨(.inl .r1b, false), [1], false, 3⟩, ⟨(.inl .r1c, false), [0, 1, 4, 5], false, 4⟩, ⟨(.inl .r1b, false), [3], false, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩,
      ⟨(.inl .r2b, false), [0, 1, 3], true, 1⟩, ⟨(.inl .r1a, false), [2, 3], false, 1⟩, ⟨(.inl .r3c, false), [2, 3], true, 2⟩, ⟨(.inl .r2e, false), [3, 0, 2, 4, 5], true, 5⟩,
      ⟨(.inl .r3d, false), [0, 1, 2, 4, 5], true, 4⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], false, 4⟩, ⟨(.inl .r2d, false), [2, 3], false, 6⟩,
      ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r2b, false), [0, 1, 2], true, 5⟩, ⟨(.inl .r2b, false), [0, 1, 3], true, 6⟩, ⟨(.inl .r3c, true), [2, 3], false, 4⟩,
      ⟨(.inl .r3c, false), [2, 3], true, 5⟩, ⟨(.inl .r2d, false), [2, 3], false, 4⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 6⟩,
      ⟨(.inr .k11, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r1a, false), [1, 3], true, 6⟩, ⟨(.inl .r2d, false), [1, 3], false, 8⟩, ⟨(.inl .r1b, false), [1], true, 7⟩,
      ⟨(.inl .r2e, false), [3, 0, 1, 4, 5], true, 7⟩, ⟨(.inl .r3e, false), [0, 1, 3, 4, 5], true, 6⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 5⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 3⟩,
      ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 4⟩]
  | false, true, true, false =>
    [⟨(.inl .r1b, false), [0], false, 3⟩, ⟨(.inl .r1c, false), [0, 1, 4, 5], false, 4⟩, ⟨(.inl .r1b, false), [1], false, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩,
      ⟨(.inl .r3c, false), [0, 1], true, 1⟩, ⟨(.inl .r1a, false), [2, 3], false, 1⟩, ⟨(.inl .r2b, false), [2, 3, 0], true, 2⟩, ⟨(.inl .r2e, false), [1, 0, 2, 4, 5], true, 5⟩,
      ⟨(.inl .r3d, false), [0, 1, 2, 4, 5], true, 4⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], false, 4⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 4⟩,
      ⟨(.inl .r3c, false), [0, 1], true, 5⟩, ⟨(.inl .r2b, false), [0, 1, 2], true, 6⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .k22, false), [0, 1, 2, 3], true, 5⟩,
      ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r3b, false), [0, 1, 3], true, 5⟩, ⟨(.inl .r3b, false), [1, 2, 3], false, 6⟩, ⟨(.inl .r3a, false), [1, 2, 3], false, 6⟩,
      ⟨(.inl .r2b, false), [1, 3, 0], true, 7⟩, ⟨(.inl .r3c, true), [1, 3], false, 8⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 9⟩, ⟨(.inl .r2d, false), [2, 3], false, 8⟩,
      ⟨(.inl .r3c, false), [1, 3], true, 10⟩, ⟨(.inl .r1a, false), [1, 3], true, 11⟩, ⟨(.inl .r2d, false), [1, 3], false, 9⟩, ⟨(.inl .r2d, false), [1, 2], false, 8⟩,
      ⟨(.inl .r2d, false), [1, 2], true, 8⟩, ⟨(.inl .r2d, false), [1, 3], true, 9⟩, ⟨(.inl .r1b, false), [1], true, 10⟩, ⟨(.inl .r1b, false), [3], true, 9⟩,
      ⟨(.inl .r2d, false), [0, 2], false, 8⟩, ⟨(.inl .r1b, false), [0], true, 7⟩, ⟨(.inl .r1a, false), [0, 1], false, 7⟩, ⟨(.inl .r3b, false), [0, 1, 2], true, 6⟩,
      ⟨(.inl .r3a, true), [0, 2, 3], true, 5⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 6⟩, ⟨(.inl .r3b, false), [1, 2, 3], false, 6⟩, ⟨(.inl .r2e, false), [2, 0, 1, 4, 5], true, 9⟩,
      ⟨(.inl .r4a, false), [0, 1, 4, 5], true, 8⟩, ⟨(.inl .r3e, false), [0, 1, 2, 4, 5], true, 7⟩, ⟨(.inl .r3e, false), [0, 2, 3, 4, 5], true, 6⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 5⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], true, 7⟩, ⟨(.inl .r2a, false), [1, 5, 2, 3], false, 8⟩, ⟨(.inl .r3a, false), [1, 3, 5], true, 7⟩, ⟨(.inl .r3b, false), [1, 3, 5], true, 7⟩,
      ⟨(.inl .r3b, false), [2, 3, 5], true, 8⟩, ⟨(.inl .r2d, false), [2, 5], false, 11⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 4⟩]
  | true, false, false, true =>
    [⟨(.inl .r1b, false), [1], false, 3⟩, ⟨(.inl .r1c, false), [0, 1, 4, 5], false, 4⟩, ⟨(.inl .r1b, false), [3], false, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩,
      ⟨(.inl .r2b, false), [0, 1, 3], true, 1⟩, ⟨(.inl .r1a, false), [2, 3], false, 1⟩, ⟨(.inl .r3c, false), [2, 3], true, 2⟩, ⟨(.inl .r2e, false), [3, 0, 2, 4, 5], true, 5⟩,
      ⟨(.inl .r3d, false), [0, 1, 2, 4, 5], true, 4⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], false, 4⟩, ⟨(.inl .r2d, false), [0, 3], false, 6⟩,
      ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r3c, true), [0, 1], false, 5⟩, ⟨(.inl .r2b, false), [0, 1, 3], true, 6⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 7⟩,
      ⟨(.inr .k21, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r3b, false), [0, 1, 3], true, 5⟩, ⟨(.inl .r3b, false), [1, 2, 3], false, 6⟩,
      ⟨(.inl .r3a, false), [1, 2, 3], false, 6⟩, ⟨(.inl .r1a, false), [1, 3], true, 7⟩, ⟨(.inl .r2d, false), [1, 3], false, 8⟩, ⟨(.inl .r1b, false), [1], true, 7⟩,
      ⟨(.inl .r1a, false), [0, 1], false, 7⟩, ⟨(.inl .r3b, false), [0, 1, 2], true, 6⟩, ⟨(.inl .r3a, true), [0, 2, 3], true, 5⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 6⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], false, 6⟩, ⟨(.inl .r2e, false), [3, 0, 1, 4, 5], true, 9⟩, ⟨(.inl .r4a, false), [0, 1, 4, 5], true, 8⟩, ⟨(.inl .r3e, false), [0, 1, 2, 4, 5], true, 7⟩,
      ⟨(.inl .r3e, false), [0, 2, 3, 4, 5], true, 6⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 5⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 7⟩, ⟨(.inl .r2a, false), [1, 5, 2, 3], false, 8⟩,
      ⟨(.inl .r3a, false), [1, 3, 5], true, 7⟩, ⟨(.inl .r3b, false), [1, 3, 5], true, 7⟩, ⟨(.inl .r3b, false), [2, 3, 5], true, 8⟩, ⟨(.inl .r2d, false), [3, 5], false, 11⟩,
      ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 4⟩]
  | true, false, true, false =>
    [⟨(.inl .r1b, false), [0], false, 3⟩, ⟨(.inl .r1c, false), [0, 1, 4, 5], false, 4⟩, ⟨(.inl .r1b, false), [1], false, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩,
      ⟨(.inl .r3c, false), [0, 1], true, 1⟩, ⟨(.inl .r1a, false), [2, 3], false, 1⟩, ⟨(.inl .r2b, false), [2, 3, 0], true, 2⟩, ⟨(.inl .r2e, false), [1, 0, 2, 4, 5], true, 5⟩,
      ⟨(.inl .r3d, false), [0, 1, 2, 4, 5], true, 4⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], false, 4⟩, ⟨(.inl .r2d, false), [0, 1], false, 6⟩,
      ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r3c, true), [0, 1], false, 5⟩, ⟨(.inl .r3c, false), [0, 1], true, 6⟩, ⟨(.inl .r2d, false), [0, 1], false, 5⟩,
      ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], false, 5⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 6⟩, ⟨(.inl .r2d, false), [1, 2], true, 7⟩, ⟨(.inl .r2d, false), [1, 3], true, 8⟩, ⟨(.inl .r2d, false), [2, 3], true, 7⟩,
      ⟨(.inl .r3c, false), [1, 3], false, 9⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 8⟩, ⟨(.inl .r3c, true), [1, 3], true, 7⟩, ⟨(.inl .r2b, false), [1, 3, 0], false, 6⟩,
      ⟨(.inl .r2d, false), [1, 2], true, 8⟩, ⟨(.inl .r2d, false), [1, 3], true, 9⟩, ⟨(.inl .r1b, false), [1], true, 10⟩, ⟨(.inl .r1b, false), [3], true, 9⟩,
      ⟨(.inl .r2d, false), [0, 2], false, 8⟩, ⟨(.inl .r1b, false), [0], true, 7⟩, ⟨(.inl .r2e, false), [2, 0, 1, 4, 5], true, 7⟩, ⟨(.inl .r3e, false), [0, 1, 3, 4, 5], true, 6⟩,
      ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 5⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 4⟩]
  | true, true, false, false =>
    [⟨(.inl .r1c, false), [0, 1, 4, 5], false, 4⟩, ⟨(.inl .r1b, false), [3], false, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩, ⟨(.inl .r2b, false), [0, 1, 3], true, 1⟩,
      ⟨(.inl .r1a, false), [1, 2], false, 1⟩, ⟨(.inl .r2b, false), [1, 2, 3], true, 2⟩, ⟨(.inl .r1a, false), [2, 3], false, 2⟩, ⟨(.inl .r3c, false), [2, 3], true, 3⟩,
      ⟨(.inl .r3a, true), [1, 2, 3], false, 1⟩, ⟨(.inl .r3c, false), [1, 2], true, 2⟩, ⟨(.inl .r1a, false), [4, 5], false, 2⟩, ⟨(.inl .r2b, false), [4, 5, 1], true, 3⟩,
      ⟨(.inl .r2e, false), [3, 0, 2, 4, 5], true, 9⟩, ⟨(.inl .r3d, false), [0, 1, 2, 4, 5], true, 8⟩, ⟨(.inl .r4a, false), [1, 2, 4, 5], true, 7⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 6⟩,
      ⟨(.inl .r3d, false), [1, 2, 3, 4, 5], true, 5⟩, ⟨(.inl .r4c, false), [2, 3, 4, 5], true, 4⟩, ⟨(.inl .r2a, false), [1, 2, 3, 5], false, 5⟩, ⟨(.inl .r3b, false), [2, 3, 5], true, 6⟩,
      ⟨(.inl .r3b, false), [2, 3, 5], false, 6⟩, ⟨(.inl .r3a, false), [2, 3, 5], false, 6⟩, ⟨(.inl .r1a, false), [2, 5], true, 7⟩, ⟨(.inl .r2b, false), [0, 1, 5], false, 8⟩,
      ⟨(.inl .r2b, false), [0, 1, 2], false, 7⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], false, 6⟩, ⟨(.inl .r3b, false), [0, 1, 2], true, 5⟩, ⟨(.inl .r2d, false), [3, 5], false, 9⟩,
      ⟨(.inl .r2d, false), [0, 5], false, 10⟩, ⟨(.inl .r2d, false), [0, 3], false, 9⟩, ⟨(.inl .r2d, false), [0, 2], false, 8⟩, ⟨(.inl .r2d, false), [2, 3], true, 9⟩,
      ⟨(.inl .r2d, false), [2, 5], true, 10⟩, ⟨(.inl .r1b, false), [2], true, 11⟩, ⟨(.inl .r3b, false), [0, 1, 2], false, 5⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 6⟩,
      ⟨(.inl .r3c, true), [0, 1], false, 7⟩, ⟨(.inl .r2b, false), [0, 1, 3], true, 8⟩, ⟨(.inl .r3a, true), [1, 2, 3], false, 5⟩, ⟨(.inl .r3c, true), [1, 2], false, 6⟩,
      ⟨(.inl .r2b, false), [1, 2, 3], true, 7⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 5⟩, ⟨(.inl .r3c, false), [1, 3], true, 6⟩, ⟨(.inl .r2d, false), [1, 2], false, 5⟩,
      ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 10⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 9⟩, ⟨(.inr .ksym2, false), [0, 1, 2, 3], true, 8⟩, ⟨(.inr .ksym6, false), [0, 1, 2, 3], true, 7⟩,
      ⟨(.inr .k31, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r3a, false), [1, 2, 3], false, 8⟩, ⟨(.inl .r1a, false), [1, 2], true, 7⟩, ⟨(.inl .r1a, false), [1, 3], true, 7⟩,
      ⟨(.inl .r2d, false), [3, 5], true, 8⟩, ⟨(.inl .r1a, false), [0, 1], false, 9⟩, ⟨(.inl .r2b, false), [0, 1, 5], false, 8⟩, ⟨(.inl .r3c, true), [0, 1], true, 7⟩,
      ⟨(.inl .r3a, true), [0, 1, 3], true, 6⟩, ⟨(.inl .r2e, false), [3, 0, 1, 4, 5], true, 11⟩, ⟨(.inl .r4a, false), [0, 1, 4, 5], true, 10⟩, ⟨(.inr .k32, false), [0, 1, 4, 5], true, 8⟩,
      ⟨(.inl .r3e, false), [0, 1, 3, 4, 5], true, 7⟩, ⟨(.inl .r3d, false), [0, 1, 3, 4, 5], true, 6⟩, ⟨(.inl .r3b, true), [0, 1, 3], true, 7⟩, ⟨(.inl .r3a, false), [0, 3, 5], true, 8⟩,
      ⟨(.inl .r3b, false), [0, 3, 5], true, 8⟩, ⟨(.inl .r2a, false), [0, 5, 1, 3], false, 7⟩, ⟨(.inl .r3b, true), [1, 3, 5], true, 8⟩, ⟨(.inl .r3a, true), [1, 4, 5], true, 9⟩,
      ⟨(.inl .r2a, false), [1, 4, 3, 5], false, 8⟩, ⟨(.inl .r3c, true), [1, 5], true, 14⟩, ⟨(.inl .r2b, false), [1, 5, 4], false, 13⟩, ⟨(.inl .r3c, false), [1, 5], false, 12⟩,
      ⟨(.inl .r2b, false), [1, 5, 0], false, 11⟩, ⟨(.inl .r3b, true), [1, 4, 5], false, 10⟩, ⟨(.inl .r2a, false), [1, 4, 3, 5], false, 9⟩, ⟨(.inl .r1a, false), [1, 4], true, 8⟩,
      ⟨(.inl .r2d, false), [4, 5], false, 11⟩, ⟨(.inl .r2d, false), [1, 5], false, 12⟩, ⟨(.inl .r2d, false), [1, 4], false, 11⟩, ⟨(.inl .r2d, false), [1, 4], true, 11⟩,
      ⟨(.inl .r2d, false), [1, 5], true, 12⟩, ⟨(.inl .r1b, false), [1], true, 13⟩, ⟨(.inl .r1b, false), [5], true, 12⟩, ⟨(.inl .r2d, false), [3, 4], false, 11⟩,
      ⟨(.inl .r5a, false), [0, 1, 2, 3, 4, 5], true, 5⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 4⟩]
  | true, true, true, true =>
    [⟨(.inl .r1b, false), [1], false, 4⟩, ⟨(.inl .r1b, false), [0], false, 4⟩, ⟨(.inl .r2d, false), [0, 1], true, 5⟩, ⟨(.inl .r2d, false), [0, 1], true, 4⟩,
      ⟨(.inl .r1c, false), [0, 1, 4, 5], false, 6⟩, ⟨(.inl .r1b, false), [3], false, 0⟩, ⟨(.inl .r1a, false), [0, 2], false, 0⟩, ⟨(.inl .r2b, false), [0, 2, 3], true, 1⟩,
      ⟨(.inl .r1a, false), [2, 3], false, 1⟩, ⟨(.inl .r3c, false), [2, 3], true, 2⟩, ⟨(.inl .r3a, true), [0, 2, 3], false, 0⟩, ⟨(.inl .r3c, false), [0, 2], true, 1⟩,
      ⟨(.inl .r1a, false), [4, 5], false, 1⟩, ⟨(.inl .r2b, false), [4, 5, 0], true, 2⟩, ⟨(.inl .r2e, false), [3, 0, 2, 4, 5], true, 7⟩, ⟨(.inl .r4a, false), [0, 2, 4, 5], true, 6⟩,
      ⟨(.inl .r3e, false), [0, 2, 3, 4, 5], true, 5⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r4c, false), [2, 3, 4, 5], true, 3⟩, ⟨(.inl .r2a, false), [0, 2, 3, 5], false, 4⟩,
      ⟨(.inl .r3b, false), [2, 3, 5], true, 5⟩, ⟨(.inl .r3b, false), [2, 3, 5], false, 5⟩, ⟨(.inl .r3a, false), [2, 3, 5], false, 5⟩, ⟨(.inl .r1a, false), [2, 5], true, 6⟩,
      ⟨(.inl .r2d, false), [3, 5], false, 7⟩, ⟨(.inl .r2d, false), [0, 5], false, 8⟩, ⟨(.inl .r2d, false), [0, 3], false, 7⟩, ⟨(.inl .r2d, false), [0, 2], false, 6⟩,
      ⟨(.inl .r2d, false), [2, 3], true, 7⟩, ⟨(.inl .r2d, false), [2, 5], true, 8⟩, ⟨(.inl .r1b, false), [2], true, 9⟩, ⟨(.inl .r3a, true), [0, 2, 3], false, 4⟩,
      ⟨(.inl .r3c, true), [0, 2], false, 5⟩, ⟨(.inl .r2b, false), [0, 2, 3], true, 6⟩, ⟨(.inl .r2b, false), [0, 3, 2], true, 4⟩, ⟨(.inl .r3c, false), [0, 3], true, 5⟩,
      ⟨(.inl .r2d, false), [0, 2], false, 4⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 8⟩, ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 6⟩,
      ⟨(.inr .k22, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r2d, false), [1, 2], true, 8⟩, ⟨(.inl .r2d, false), [1, 3], true, 9⟩, ⟨(.inl .r2d, false), [2, 3], true, 8⟩,
      ⟨(.inl .r3c, false), [1, 3], false, 10⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 9⟩, ⟨(.inl .r3c, true), [1, 3], true, 8⟩, ⟨(.inl .r2b, false), [1, 3, 0], false, 7⟩,
      ⟨(.inl .r3b, true), [1, 2, 3], false, 6⟩, ⟨(.inl .r2b, false), [2, 3, 0], true, 7⟩, ⟨(.inl .r2b, false), [2, 3, 1], true, 8⟩, ⟨(.inl .r3c, true), [2, 3], false, 9⟩,
      ⟨(.inl .r3c, false), [2, 3], true, 10⟩, ⟨(.inl .r1a, false), [2, 3], true, 11⟩, ⟨(.inl .r2d, false), [2, 3], false, 9⟩, ⟨(.inl .r2d, false), [1, 2], true, 8⟩,
      ⟨(.inl .r2d, false), [1, 3], true, 9⟩, ⟨(.inl .r2d, false), [2, 3], true, 8⟩, ⟨(.inl .r3c, false), [1, 3], false, 10⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 9⟩,
      ⟨(.inl .r3c, true), [1, 3], true, 8⟩, ⟨(.inl .r2b, false), [1, 3, 0], false, 7⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 6⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 6⟩,
      ⟨(.inl .r2d, false), [1, 2], true, 9⟩, ⟨(.inl .r2d, false), [1, 3], true, 10⟩, ⟨(.inl .r1b, false), [1], true, 11⟩, ⟨(.inl .r2d, false), [2, 3], false, 10⟩,
      ⟨(.inl .r1b, false), [2], true, 9⟩, ⟨(.inl .r2b, false), [2, 3, 0], true, 7⟩, ⟨(.inl .r3c, false), [2, 3], true, 8⟩, ⟨(.inl .r1a, false), [2, 3], true, 9⟩,
      ⟨(.inl .r1b, false), [2], true, 8⟩, ⟨(.inl .r2d, false), [1, 5], false, 9⟩, ⟨(.inl .r2d, false), [1, 3], false, 8⟩, ⟨(.inl .r2d, false), [0, 1], true, 7⟩,
      ⟨(.inl .r2d, false), [0, 3], true, 8⟩, ⟨(.inl .r2d, false), [0, 5], true, 9⟩, ⟨(.inl .r1b, false), [0], true, 10⟩, ⟨(.inl .r2d, false), [3, 5], true, 8⟩,
      ⟨(.inl .r3c, true), [1, 3], false, 6⟩, ⟨(.inl .r2b, false), [1, 3, 5], true, 7⟩, ⟨(.inl .r2b, false), [0, 1, 3], true, 5⟩, ⟨(.inl .r2b, false), [0, 1, 5], true, 6⟩,
      ⟨(.inl .r2e, false), [3, 0, 1, 4, 5], true, 9⟩, ⟨(.inl .r3e, false), [0, 1, 3, 4, 5], true, 8⟩, ⟨(.inl .r3d, false), [0, 1, 3, 4, 5], true, 7⟩, ⟨(.inr .k21, false), [1, 3, 4, 5], true, 5⟩,
      ⟨(.inl .r2a, false), [0, 1, 4, 5], false, 7⟩, ⟨(.inl .r3b, false), [0, 1, 3], true, 6⟩, ⟨(.inl .r2a, false), [1, 3, 4, 5], false, 8⟩, ⟨(.inl .r1a, false), [1, 3], true, 7⟩,
      ⟨(.inl .r5a, false), [0, 1, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 3⟩]
  | _, _, _, _ => []

theorem chk323_0102 : ∀ x y p q : Bool, xor (xor (xor x y) p) q = false →
    checkD (Gen.k 0 2 4 5 (by decide) (by decide) (by decide) :: (negw x 0 ++ negw y 2) ++ [Gen.k 0 1 2 3 (by decide) (by decide) (by decide)])
      (X323_0102 x y p q ++ Gen.k 0 1 2 4 (by decide) (by decide) (by decide) :: Y323_0102 x y p q ++
        Gen.k 0 1 4 5 (by decide) (by decide) (by decide) :: (negw p 0 ++ negw q 1)) (S323_0102 x y p q) = true := by
  decide +kernel

theorem tag323_0102 : ∀ x y p q : Bool, ∀ g ∈ X323_0102 x y p q ++ Y323_0102 x y p q, g.tag ≠ 2 := by
  decide

/-- Subcase 3.2.3 with `{a,b} = {0,1}`, `{α,β} = {0,2}` (from `0`). -/
theorem rel323_0102 {a0 a1 a2 a3 c d : Fin n} (h1 : a0 < a1) (h2 : a1 < a2) (h3 : a2 < a3) (h4 : a3 < c) (h5 : c < d) (x y p q : Bool)
    (hpar : xor (xor (xor x y) p) q = false) :
    ∃ Xw Yw : List (Gen n), (∀ g ∈ Xw ++ Yw, g.tag ≠ 2 ∧ extent g ≤ d.val) ∧
      Derivable (Table1 n)
        (FreeMonoid.ofList (Gen.k a0 a2 c d (h1.trans h2) (h3.trans h4) h5 :: (negw x a0 ++ negw y a2) ++
          [Gen.k a0 a1 a2 a3 h1 h2 h3]))
        (FreeMonoid.ofList (Xw ++ Gen.k a0 a1 a2 c h1 h2 (h3.trans h4) :: Yw ++
          Gen.k a0 a1 c d h1 (h2.trans (h3.trans h4)) h5 :: (negw p a0 ++ negw q a1))) := by
  refine ⟨(X323_0102 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)),
    (Y323_0102 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)), ?_, ?_⟩
  · intro g hg
    rw [← List.map_append] at hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    refine ⟨by rw [tag_rename]; exact tag323_0102 x y p q g' hg', ?_⟩
    have := extent_rename_le (emb6 h1 h2 h3 h4 h5) g' 5 (extent_le_last g')
    rwa [emb6_5] at this
  · have hh := derivable_rename (emb6 h1 h2 h3 h4 h5) (checkD_sound (chk323_0102 x y p q hpar))
    rw [renW_ofList, renW_ofList] at hh
    convert hh using 2 <;>
      simp only [List.map_append, List.map_cons, List.map_nil, negw_rename, Gen.rename, emb6_0,
        emb6_1, emb6_2, emb6_3, emb6_4, emb6_5, List.cons_append, List.nil_append,
        List.append_assoc]

/-- `X` for `{a,b} = {0,1}`, `{α,β} = {1,3}`. -/
def X323_0113 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, true => [Gen.x 1 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 2]
  | false, false, true, false => [Gen.x 1 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 2]
  | false, true, false, false => [Gen.neg 2]
  | false, true, true, true => [Gen.x 0 2 (by decide), Gen.neg 0]
  | true, false, false, false => [Gen.neg 2]
  | true, false, true, true => [Gen.neg 0]
  | true, true, false, true => [Gen.x 1 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 2]
  | true, true, true, false => [Gen.x 0 2 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 0]
  | _, _, _, _ => []

/-- `Y` for `{a,b} = {0,1}`, `{α,β} = {1,3}`. -/
def Y323_0113 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, true => [Gen.x 0 3 (by decide), Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide)]
  | false, false, true, false => [Gen.x 0 5 (by decide), Gen.x 1 4 (by decide), Gen.x 2 5 (by decide), Gen.x 3 4 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 4, Gen.neg 5]
  | false, true, false, false => [Gen.x 0 2 (by decide), Gen.x 1 3 (by decide)]
  | false, true, true, true => [Gen.x 0 2 (by decide), Gen.x 1 5 (by decide), Gen.x 3 5 (by decide), Gen.neg 1, Gen.neg 5]
  | true, false, false, false => [Gen.x 0 2 (by decide), Gen.x 1 5 (by decide), Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.neg 1, Gen.neg 5]
  | true, false, true, true => [Gen.x 0 2 (by decide), Gen.x 1 3 (by decide), Gen.neg 2, Gen.neg 3]
  | true, true, false, true => [Gen.x 0 5 (by decide), Gen.x 1 2 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 0, Gen.neg 4]
  | true, true, true, false => [Gen.x 0 3 (by decide), Gen.x 1 2 (by decide), Gen.x 4 5 (by decide)]
  | _, _, _, _ => []

/-- The chains for `{a,b} = {0,1}`, `{α,β} = {1,3}`. -/
def S323_0113 : Bool → Bool → Bool → Bool → List (GStep ((Fam ⊕ MFam) × Bool) 6)
  | false, false, false, true =>
    [⟨(.inl .r1b, false), [1], false, 2⟩, ⟨(.inl .r1c, false), [0, 1, 4, 5], false, 3⟩, ⟨(.inl .r1b, false), [2], false, 0⟩, ⟨(.inl .r1a, false), [1, 3], false, 0⟩,
      ⟨(.inl .r2b, false), [1, 3, 2], true, 1⟩, ⟨(.inl .r1a, false), [4, 5], false, 1⟩, ⟨(.inl .r2b, false), [4, 5, 2], true, 2⟩, ⟨(.inl .r2e, false), [2, 1, 3, 4, 5], true, 5⟩,
      ⟨(.inl .r4a, false), [1, 3, 4, 5], true, 4⟩, ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 3⟩, ⟨(.inl .r1a, false), [3, 5], true, 4⟩, ⟨(.inl .r2d, false), [2, 5], false, 5⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 4⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 6⟩, ⟨(.inr .k11, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r2d, false), [1, 5], false, 7⟩,
      ⟨(.inl .r3c, true), [1, 3], false, 6⟩, ⟨(.inl .r2b, false), [1, 3, 5], true, 7⟩, ⟨(.inl .r2b, false), [0, 2, 3], true, 5⟩, ⟨(.inl .r2b, false), [0, 2, 5], true, 6⟩,
      ⟨(.inl .r3e, false), [0, 1, 3, 4, 5], true, 8⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 7⟩, ⟨(.inr .k21, false), [2, 3, 4, 5], true, 5⟩, ⟨(.inl .r2a, false), [0, 2, 4, 5], false, 7⟩,
      ⟨(.inl .r3b, false), [0, 2, 3], true, 6⟩, ⟨(.inl .r2a, false), [1, 3, 4, 5], false, 8⟩, ⟨(.inl .r3b, true), [1, 2, 3], false, 7⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 3⟩,
      ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 4⟩]
  | false, false, true, false =>
    [⟨(.inl .r1b, false), [0], false, 2⟩, ⟨(.inl .r1c, false), [0, 1, 4, 5], false, 3⟩, ⟨(.inl .r1b, false), [2], false, 0⟩, ⟨(.inl .r1a, false), [1, 3], false, 0⟩,
      ⟨(.inl .r2b, false), [1, 3, 2], true, 1⟩, ⟨(.inl .r1a, false), [4, 5], false, 1⟩, ⟨(.inl .r2b, false), [4, 5, 2], true, 2⟩, ⟨(.inl .r2e, false), [2, 1, 3, 4, 5], true, 5⟩,
      ⟨(.inl .r4a, false), [1, 3, 4, 5], true, 4⟩, ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 3⟩, ⟨(.inl .r1a, false), [3, 5], true, 4⟩, ⟨(.inl .r2d, false), [2, 5], false, 5⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 4⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 6⟩, ⟨(.inr .k11, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r2d, false), [0, 5], false, 7⟩,
      ⟨(.inr .k32, false), [0, 1, 4, 5], true, 7⟩, ⟨(.inl .r3e, false), [0, 1, 3, 4, 5], true, 6⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 5⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], true, 6⟩,
      ⟨(.inl .r3a, false), [0, 2, 5], true, 7⟩, ⟨(.inl .r3b, false), [0, 2, 5], true, 7⟩, ⟨(.inl .r2a, false), [0, 5, 1, 3], false, 6⟩, ⟨(.inl .r2a, false), [1, 3, 2, 5], true, 7⟩,
      ⟨(.inl .r3a, false), [1, 3, 4], true, 8⟩, ⟨(.inl .r3b, false), [1, 3, 4], true, 8⟩, ⟨(.inl .r2a, false), [1, 4, 2, 5], false, 7⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 3⟩,
      ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 4⟩]
  | false, true, false, false =>
    [⟨(.inl .r1c, false), [0, 1, 4, 5], false, 3⟩, ⟨(.inl .r1b, false), [2], false, 0⟩, ⟨(.inl .r2e, false), [2, 1, 3, 4, 5], true, 1⟩, ⟨(.inr .k11, false), [0, 1, 2, 3], true, 2⟩,
      ⟨(.inl .r3e, false), [0, 1, 3, 4, 5], true, 4⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 1⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 2⟩]
  | false, true, true, true =>
    [⟨(.inl .r1b, false), [1], false, 3⟩, ⟨(.inl .r1b, false), [0], false, 3⟩, ⟨(.inl .r2d, false), [0, 1], true, 4⟩, ⟨(.inl .r2d, false), [0, 1], true, 3⟩,
      ⟨(.inl .r1c, false), [0, 1, 4, 5], false, 5⟩, ⟨(.inl .r1b, false), [2], false, 0⟩, ⟨(.inl .r1a, false), [0, 2], false, 0⟩, ⟨(.inl .r3c, false), [0, 2], true, 1⟩,
      ⟨(.inl .r2e, false), [2, 1, 3, 4, 5], true, 3⟩, ⟨(.inl .r2c, false), [0, 2, 1, 3, 4, 5], true, 2⟩, ⟨(.inl .r3c, false), [0, 2], true, 3⟩, ⟨(.inl .r2b, false), [0, 2, 3], true, 4⟩,
      ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inr .k32, false), [0, 1, 2, 3], true, 3⟩, ⟨(.inl .r2d, false), [2, 3], true, 8⟩, ⟨(.inl .r3c, false), [2, 3], false, 9⟩,
      ⟨(.inl .r3c, true), [2, 3], true, 8⟩, ⟨(.inl .r2b, false), [2, 3, 1], false, 7⟩, ⟨(.inl .r2b, false), [2, 3, 0], false, 6⟩, ⟨(.inl .r2d, false), [2, 3], false, 10⟩,
      ⟨(.inl .r1b, false), [2], true, 9⟩, ⟨(.inl .r1b, false), [3], true, 9⟩, ⟨(.inl .r1b, false), [1], true, 8⟩, ⟨(.inl .r1b, false), [0], true, 7⟩,
      ⟨(.inl .r3a, true), [1, 2, 3], false, 5⟩, ⟨(.inl .r3b, false), [0, 1, 3], false, 4⟩, ⟨(.inl .r3a, true), [0, 1, 2], false, 5⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], false, 4⟩,
      ⟨(.inl .r4a, false), [0, 1, 4, 5], true, 6⟩, ⟨(.inl .r3e, false), [0, 1, 3, 4, 5], true, 5⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r3a, false), [1, 3, 5], true, 6⟩,
      ⟨(.inl .r3b, false), [1, 3, 5], true, 6⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 2⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 3⟩]
  | true, false, false, false =>
    [⟨(.inl .r1c, false), [0, 1, 4, 5], false, 3⟩, ⟨(.inl .r1b, false), [2], false, 0⟩, ⟨(.inl .r2e, false), [2, 1, 3, 4, 5], true, 1⟩, ⟨(.inl .r2d, false), [1, 2], false, 2⟩,
      ⟨(.inr .k31, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inl .r1a, false), [0, 1], false, 5⟩, ⟨(.inl .r3b, false), [0, 1, 2], true, 4⟩, ⟨(.inl .r3a, true), [0, 2, 3], true, 3⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], true, 4⟩, ⟨(.inl .r3b, false), [1, 2, 3], false, 4⟩, ⟨(.inl .r4a, false), [0, 1, 4, 5], true, 6⟩, ⟨(.inl .r3e, false), [0, 1, 2, 4, 5], true, 5⟩,
      ⟨(.inl .r3e, false), [0, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 5⟩, ⟨(.inl .r2a, false), [1, 5, 2, 3], false, 6⟩,
      ⟨(.inl .r3a, false), [1, 3, 5], true, 5⟩, ⟨(.inl .r3b, false), [1, 3, 5], true, 5⟩, ⟨(.inl .r3b, false), [2, 3, 5], true, 6⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 1⟩,
      ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 2⟩]
  | true, false, true, true =>
    [⟨(.inl .r1b, false), [1], false, 3⟩, ⟨(.inl .r1b, false), [0], false, 3⟩, ⟨(.inl .r2d, false), [0, 1], true, 4⟩, ⟨(.inl .r2d, false), [0, 1], true, 3⟩,
      ⟨(.inl .r1c, false), [0, 1, 4, 5], false, 5⟩, ⟨(.inl .r1b, false), [0], false, 0⟩, ⟨(.inl .r2e, false), [0, 1, 3, 4, 5], true, 1⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 2⟩,
      ⟨(.inl .r2d, false), [1, 2], true, 6⟩, ⟨(.inl .r2d, false), [1, 3], true, 7⟩, ⟨(.inl .r1b, false), [1], true, 8⟩, ⟨(.inl .r2d, false), [0, 2], true, 5⟩,
      ⟨(.inl .r2d, false), [0, 3], true, 6⟩, ⟨(.inl .r1b, false), [0], true, 7⟩, ⟨(.inl .r2d, false), [2, 3], true, 5⟩, ⟨(.inl .r2e, false), [2, 0, 1, 4, 5], true, 6⟩,
      ⟨(.inl .r2e, false), [3, 0, 1, 4, 5], true, 5⟩, ⟨(.inl .r3e, false), [0, 1, 3, 4, 5], true, 4⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r2d, false), [2, 3], false, 6⟩,
      ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 1⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 2⟩]
  | true, true, false, true =>
    [⟨(.inl .r1b, false), [1], false, 4⟩, ⟨(.inl .r1c, false), [0, 1, 4, 5], false, 5⟩, ⟨(.inl .r1b, false), [2], false, 0⟩, ⟨(.inl .r1a, false), [1, 3], false, 0⟩,
      ⟨(.inl .r2b, false), [1, 3, 2], true, 1⟩, ⟨(.inl .r1a, false), [4, 5], false, 1⟩, ⟨(.inl .r2b, false), [4, 5, 2], true, 2⟩, ⟨(.inl .r2e, false), [2, 1, 3, 4, 5], true, 5⟩,
      ⟨(.inl .r4a, false), [1, 3, 4, 5], true, 4⟩, ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 3⟩, ⟨(.inl .r1a, false), [3, 5], true, 4⟩, ⟨(.inl .r2d, false), [2, 5], false, 5⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 4⟩, ⟨(.inl .r2d, false), [1, 5], false, 6⟩, ⟨(.inl .r2d, false), [1, 3], false, 5⟩, ⟨(.inl .r2d, false), [1, 2], false, 4⟩,
      ⟨(.inl .r2d, false), [3, 5], false, 7⟩, ⟨(.inl .r1b, false), [3], true, 6⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 6⟩, ⟨(.inr .k31, false), [0, 1, 2, 3], true, 4⟩,
      ⟨(.inl .r2d, false), [1, 5], false, 7⟩, ⟨(.inl .r1a, false), [0, 1], false, 7⟩, ⟨(.inl .r3b, false), [0, 1, 2], true, 6⟩, ⟨(.inl .r3c, false), [0, 1], true, 8⟩,
      ⟨(.inl .r2b, false), [0, 1, 5], true, 9⟩, ⟨(.inl .r3a, true), [0, 2, 3], true, 5⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 6⟩, ⟨(.inl .r3b, false), [1, 2, 3], false, 6⟩,
      ⟨(.inl .r4a, false), [0, 1, 4, 5], true, 10⟩, ⟨(.inr .k32, false), [0, 1, 4, 5], true, 8⟩, ⟨(.inl .r3e, false), [0, 1, 2, 4, 5], true, 7⟩, ⟨(.inl .r3e, false), [0, 2, 3, 4, 5], true, 6⟩,
      ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 5⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 7⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], true, 6⟩, ⟨(.inl .r3b, true), [0, 2, 3], true, 7⟩,
      ⟨(.inl .r3a, false), [0, 3, 5], true, 8⟩, ⟨(.inl .r3b, false), [0, 3, 5], true, 8⟩, ⟨(.inl .r2a, false), [0, 5, 2, 3], false, 7⟩, ⟨(.inl .r2a, false), [0, 5, 1, 3], false, 6⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], false, 7⟩, ⟨(.inl .r3a, false), [1, 2, 3], false, 7⟩, ⟨(.inl .r3b, true), [1, 3, 5], true, 8⟩, ⟨(.inl .r3a, true), [1, 4, 5], true, 9⟩,
      ⟨(.inl .r2a, false), [1, 4, 3, 5], false, 8⟩, ⟨(.inl .r3a, false), [1, 2, 4], true, 7⟩, ⟨(.inl .r3b, false), [1, 2, 4], true, 7⟩, ⟨(.inl .r3b, false), [1, 2, 4], false, 7⟩,
      ⟨(.inl .r3a, false), [1, 2, 4], false, 7⟩, ⟨(.inl .r2a, false), [1, 4, 3, 5], true, 8⟩, ⟨(.inl .r3b, true), [1, 4, 5], true, 9⟩, ⟨(.inl .r2b, false), [1, 5, 0], true, 10⟩,
      ⟨(.inl .r3c, true), [1, 5], false, 11⟩, ⟨(.inl .r2b, false), [1, 5, 4], true, 12⟩, ⟨(.inl .r2d, false), [4, 5], false, 11⟩, ⟨(.inl .r3c, true), [1, 5], true, 14⟩,
      ⟨(.inl .r1a, false), [1, 5], true, 13⟩, ⟨(.inl .r2d, false), [1, 5], false, 12⟩, ⟨(.inl .r2d, false), [1, 4], false, 11⟩, ⟨(.inl .r2d, false), [1, 4], true, 11⟩,
      ⟨(.inl .r2d, false), [1, 5], true, 12⟩, ⟨(.inl .r1b, false), [1], true, 13⟩, ⟨(.inl .r1b, false), [5], true, 12⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 3⟩,
      ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 4⟩]
  | true, true, true, false =>
    [⟨(.inl .r1b, false), [0], false, 4⟩, ⟨(.inl .r1c, false), [0, 1, 4, 5], false, 5⟩, ⟨(.inl .r1b, false), [2], false, 0⟩, ⟨(.inl .r1a, false), [0, 2], false, 0⟩,
      ⟨(.inl .r3c, false), [0, 2], true, 1⟩, ⟨(.inl .r1a, false), [1, 3], false, 1⟩, ⟨(.inl .r2b, false), [1, 3, 0], true, 2⟩, ⟨(.inl .r1a, false), [4, 5], false, 2⟩,
      ⟨(.inl .r2b, false), [4, 5, 0], true, 3⟩, ⟨(.inl .r2e, false), [2, 1, 3, 4, 5], true, 7⟩, ⟨(.inl .r2c, false), [0, 2, 1, 3, 4, 5], true, 6⟩, ⟨(.inl .r4a, false), [1, 3, 4, 5], true, 5⟩,
      ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 4⟩, ⟨(.inl .r1a, false), [3, 5], true, 5⟩, ⟨(.inl .r2b, false), [0, 2, 5], false, 6⟩, ⟨(.inl .r2b, false), [0, 2, 3], false, 5⟩,
      ⟨(.inl .r2d, false), [2, 5], false, 7⟩, ⟨(.inl .r2d, false), [2, 3], false, 6⟩, ⟨(.inl .r2d, false), [1, 5], false, 8⟩, ⟨(.inl .r2d, false), [1, 3], false, 7⟩,
      ⟨(.inl .r2d, false), [1, 2], false, 6⟩, ⟨(.inl .r2d, false), [3, 5], false, 9⟩, ⟨(.inl .r1b, false), [3], true, 8⟩, ⟨(.inl .r2b, false), [0, 2, 1], true, 5⟩,
      ⟨(.inl .r3c, false), [0, 2], true, 6⟩, ⟨(.inl .r2d, false), [0, 1], false, 5⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 8⟩, ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 7⟩,
      ⟨(.inr .k12, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r2d, false), [2, 3], true, 10⟩, ⟨(.inl .r3c, false), [2, 3], false, 11⟩, ⟨(.inl .r3c, true), [2, 3], true, 10⟩,
      ⟨(.inl .r2b, false), [2, 3, 1], false, 9⟩, ⟨(.inl .r2b, false), [2, 3, 0], false, 8⟩, ⟨(.inl .r2d, false), [2, 3], false, 12⟩, ⟨(.inl .r1b, false), [2], true, 11⟩,
      ⟨(.inl .r1b, false), [3], true, 11⟩, ⟨(.inl .r2d, false), [0, 1], true, 9⟩, ⟨(.inl .r2d, false), [0, 5], true, 10⟩, ⟨(.inl .r1b, false), [0], true, 11⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], false, 7⟩, ⟨(.inl .r3c, true), [1, 2], false, 8⟩, ⟨(.inl .r2b, false), [1, 2, 5], true, 9⟩, ⟨(.inl .r3c, true), [2, 3], false, 7⟩,
      ⟨(.inl .r2b, false), [2, 3, 5], true, 8⟩, ⟨(.inl .r2b, false), [0, 2, 3], true, 6⟩, ⟨(.inl .r2b, false), [0, 2, 5], true, 7⟩, ⟨(.inl .r3e, false), [0, 1, 2, 4, 5], true, 10⟩,
      ⟨(.inl .r3e, false), [0, 2, 3, 4, 5], true, 9⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 8⟩, ⟨(.inr .k21, false), [2, 3, 4, 5], true, 6⟩, ⟨(.inl .r2a, false), [0, 2, 4, 5], false, 8⟩,
      ⟨(.inl .r3b, false), [0, 2, 3], true, 7⟩, ⟨(.inl .r2a, false), [2, 3, 4, 5], false, 9⟩, ⟨(.inl .r1a, false), [2, 3], true, 8⟩, ⟨(.inl .r2a, false), [1, 2, 4, 5], false, 8⟩,
      ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 5⟩]
  | _, _, _, _ => []

theorem chk323_0113 : ∀ x y p q : Bool, xor (xor (xor x y) p) q = true →
    checkD (Gen.k 1 3 4 5 (by decide) (by decide) (by decide) :: (negw x 1 ++ negw y 3) ++ [Gen.k 0 1 2 3 (by decide) (by decide) (by decide)])
      (X323_0113 x y p q ++ Gen.k 0 1 2 4 (by decide) (by decide) (by decide) :: Y323_0113 x y p q ++
        Gen.k 0 1 4 5 (by decide) (by decide) (by decide) :: (negw p 0 ++ negw q 1)) (S323_0113 x y p q) = true := by
  decide +kernel

theorem tag323_0113 : ∀ x y p q : Bool, ∀ g ∈ X323_0113 x y p q ++ Y323_0113 x y p q, g.tag ≠ 2 := by
  decide

/-- Subcase 3.2.3 with `{a,b} = {0,1}`, `{α,β} = {1,3}` (from `0`). -/
theorem rel323_0113 {a0 a1 a2 a3 c d : Fin n} (h1 : a0 < a1) (h2 : a1 < a2) (h3 : a2 < a3) (h4 : a3 < c) (h5 : c < d) (x y p q : Bool)
    (hpar : xor (xor (xor x y) p) q = true) :
    ∃ Xw Yw : List (Gen n), (∀ g ∈ Xw ++ Yw, g.tag ≠ 2 ∧ extent g ≤ d.val) ∧
      Derivable (Table1 n)
        (FreeMonoid.ofList (Gen.k a1 a3 c d (h2.trans h3) h4 h5 :: (negw x a1 ++ negw y a3) ++
          [Gen.k a0 a1 a2 a3 h1 h2 h3]))
        (FreeMonoid.ofList (Xw ++ Gen.k a0 a1 a2 c h1 h2 (h3.trans h4) :: Yw ++
          Gen.k a0 a1 c d h1 (h2.trans (h3.trans h4)) h5 :: (negw p a0 ++ negw q a1))) := by
  refine ⟨(X323_0113 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)),
    (Y323_0113 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)), ?_, ?_⟩
  · intro g hg
    rw [← List.map_append] at hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    refine ⟨by rw [tag_rename]; exact tag323_0113 x y p q g' hg', ?_⟩
    have := extent_rename_le (emb6 h1 h2 h3 h4 h5) g' 5 (extent_le_last g')
    rwa [emb6_5] at this
  · have hh := derivable_rename (emb6 h1 h2 h3 h4 h5) (checkD_sound (chk323_0113 x y p q hpar))
    rw [renW_ofList, renW_ofList] at hh
    convert hh using 2 <;>
      simp only [List.map_append, List.map_cons, List.map_nil, negw_rename, Gen.rename, emb6_0,
        emb6_1, emb6_2, emb6_3, emb6_4, emb6_5, List.cons_append, List.nil_append,
        List.append_assoc]

/-- `X` for `{a,b} = {0,2}`, `{α,β} = {0,1}`. -/
def X323_0201 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, false => [Gen.x 0 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 2]
  | false, false, true, true => [Gen.x 0 2 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 0]
  | false, true, false, true => [Gen.x 0 3 (by decide), Gen.x 1 3 (by decide), Gen.neg 2]
  | false, true, true, false => [Gen.x 0 2 (by decide), Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.neg 0]
  | true, false, false, true => [Gen.x 0 2 (by decide), Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.neg 2]
  | true, false, true, false => [Gen.x 0 3 (by decide), Gen.x 1 3 (by decide), Gen.neg 0]
  | true, true, false, false => [Gen.x 0 2 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 2]
  | true, true, true, true => [Gen.x 0 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 0]
  | _, _, _, _ => []

/-- `Y` for `{a,b} = {0,2}`, `{α,β} = {0,1}`. -/
def Y323_0201 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, false => [Gen.x 0 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 1]
  | false, false, true, true => [Gen.x 0 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 4]
  | false, true, false, true => [Gen.x 0 2 (by decide), Gen.x 2 3 (by decide), Gen.neg 1]
  | false, true, true, false => [Gen.x 0 2 (by decide), Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.neg 1, Gen.neg 2, Gen.neg 5]
  | true, false, false, true => [Gen.x 0 2 (by decide), Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.neg 2, Gen.neg 3, Gen.neg 5]
  | true, false, true, false => [Gen.x 0 2 (by decide), Gen.x 2 3 (by decide), Gen.neg 3]
  | true, true, false, false => [Gen.x 0 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 0, Gen.neg 3, Gen.neg 4]
  | true, true, true, true => [Gen.x 0 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 3]
  | _, _, _, _ => []

/-- The chains for `{a,b} = {0,2}`, `{α,β} = {0,1}`. -/
def S323_0201 : Bool → Bool → Bool → Bool → List (GStep ((Fam ⊕ MFam) × Bool) 6)
  | false, false, false, false =>
    [⟨(.inl .r1c, false), [0, 2, 4, 5], false, 2⟩, ⟨(.inl .r1b, false), [2], false, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩, ⟨(.inl .r2b, false), [0, 1, 2], true, 1⟩,
      ⟨(.inl .r1a, false), [1, 3], false, 1⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 2⟩, ⟨(.inl .r3a, true), [0, 1, 3], false, 0⟩, ⟨(.inl .r2b, false), [0, 1, 2], true, 1⟩,
      ⟨(.inl .r1a, false), [4, 5], false, 1⟩, ⟨(.inl .r2b, false), [4, 5, 2], true, 2⟩, ⟨(.inl .r2e, false), [2, 0, 1, 4, 5], true, 7⟩, ⟨(.inl .r4a, false), [0, 1, 4, 5], true, 6⟩,
      ⟨(.inl .r3e, false), [0, 1, 3, 4, 5], true, 5⟩, ⟨(.inl .r3d, false), [0, 1, 3, 4, 5], true, 4⟩, ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 3⟩, ⟨(.inl .r2a, false), [0, 1, 3, 5], false, 4⟩,
      ⟨(.inl .r3b, false), [1, 3, 5], true, 5⟩, ⟨(.inl .r3b, false), [1, 3, 5], false, 5⟩, ⟨(.inl .r3a, false), [1, 3, 5], false, 5⟩, ⟨(.inl .r1a, false), [1, 5], true, 6⟩,
      ⟨(.inl .r2d, false), [2, 5], false, 7⟩, ⟨(.inl .r3a, true), [0, 1, 3], false, 4⟩, ⟨(.inl .r3c, false), [0, 1], true, 5⟩, ⟨(.inl .r2b, false), [0, 1, 2], true, 6⟩,
      ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 8⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .k22, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 4⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], false, 5⟩, ⟨(.inl .r3a, false), [1, 2, 3], false, 5⟩, ⟨(.inl .r1a, false), [1, 3], true, 6⟩, ⟨(.inl .r2b, false), [0, 1, 2], false, 7⟩,
      ⟨(.inl .r3c, true), [0, 1], true, 6⟩, ⟨(.inl .r3b, false), [0, 1, 2], true, 5⟩, ⟨(.inl .r3c, false), [2, 3], false, 8⟩, ⟨(.inl .r2b, false), [2, 3, 0], false, 7⟩,
      ⟨(.inl .r2d, false), [0, 3], false, 9⟩, ⟨(.inl .r1b, false), [0], true, 8⟩, ⟨(.inl .r2d, false), [1, 3], false, 8⟩, ⟨(.inl .r2d, false), [2, 3], false, 9⟩,
      ⟨(.inl .r1b, false), [3], true, 10⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 9⟩, ⟨(.inl .r3c, false), [1, 3], false, 8⟩, ⟨(.inl .r3b, true), [1, 2, 3], false, 7⟩,
      ⟨(.inl .r1a, false), [1, 2], true, 6⟩, ⟨(.inl .r2d, false), [2, 3], false, 7⟩, ⟨(.inl .r2d, false), [1, 3], false, 8⟩, ⟨(.inl .r2d, false), [1, 2], false, 7⟩,
      ⟨(.inl .r1b, false), [3], true, 9⟩, ⟨(.inl .r2d, false), [1, 2], true, 7⟩, ⟨(.inl .r2d, false), [1, 5], true, 8⟩, ⟨(.inl .r3c, true), [2, 3], false, 6⟩,
      ⟨(.inl .r2b, false), [2, 3, 5], true, 7⟩, ⟨(.inl .r2b, false), [0, 2, 3], true, 5⟩, ⟨(.inl .r2b, false), [0, 2, 5], true, 6⟩, ⟨(.inl .r2e, false), [1, 0, 2, 4, 5], true, 9⟩,
      ⟨(.inl .r3e, false), [0, 2, 3, 4, 5], true, 8⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 7⟩, ⟨(.inr .k21, false), [2, 3, 4, 5], true, 5⟩, ⟨(.inl .r2a, false), [0, 2, 4, 5], false, 7⟩,
      ⟨(.inl .r3b, false), [0, 2, 3], true, 6⟩, ⟨(.inl .r2a, false), [2, 3, 4, 5], false, 8⟩, ⟨(.inl .r1a, false), [2, 3], true, 7⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 3⟩,
      ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 4⟩]
  | false, false, true, true =>
    [⟨(.inl .r1b, false), [2], false, 2⟩, ⟨(.inl .r1b, false), [0], false, 2⟩, ⟨(.inl .r2d, false), [0, 2], true, 3⟩, ⟨(.inl .r2d, false), [0, 2], true, 2⟩,
      ⟨(.inl .r1c, false), [0, 2, 4, 5], false, 4⟩, ⟨(.inl .r1b, false), [2], false, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩, ⟨(.inl .r2b, false), [0, 1, 2], true, 1⟩,
      ⟨(.inl .r1a, false), [1, 2], false, 1⟩, ⟨(.inl .r3c, false), [1, 2], true, 2⟩, ⟨(.inl .r3a, true), [0, 1, 2], false, 0⟩, ⟨(.inl .r3c, false), [0, 1], true, 1⟩,
      ⟨(.inl .r1a, false), [2, 3], false, 1⟩, ⟨(.inl .r2b, false), [2, 3, 0], true, 2⟩, ⟨(.inl .r1a, false), [4, 5], false, 2⟩, ⟨(.inl .r2b, false), [4, 5, 0], true, 3⟩,
      ⟨(.inl .r2e, false), [2, 0, 1, 4, 5], true, 9⟩, ⟨(.inl .r4a, false), [0, 1, 4, 5], true, 8⟩, ⟨(.inl .r3e, false), [0, 1, 2, 4, 5], true, 7⟩, ⟨(.inl .r3d, false), [0, 1, 2, 4, 5], true, 6⟩,
      ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 5⟩, ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 4⟩, ⟨(.inl .r3b, false), [2, 3, 5], true, 5⟩, ⟨(.inl .r2a, false), [0, 1, 3, 5], false, 6⟩,
      ⟨(.inl .r2a, false), [0, 1, 2, 5], false, 5⟩, ⟨(.inl .r2a, false), [1, 2, 3, 5], false, 7⟩, ⟨(.inl .r3b, false), [1, 2, 5], true, 6⟩, ⟨(.inl .r3b, false), [2, 3, 5], false, 7⟩,
      ⟨(.inl .r2a, false), [1, 5, 2, 3], false, 8⟩, ⟨(.inl .r3b, true), [1, 3, 5], false, 7⟩, ⟨(.inl .r3a, true), [1, 3, 5], false, 7⟩, ⟨(.inl .r1a, false), [1, 5], true, 6⟩,
      ⟨(.inl .r2d, false), [2, 5], false, 9⟩, ⟨(.inl .r3a, true), [0, 1, 3], false, 5⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inl .r3c, false), [0, 1], true, 7⟩,
      ⟨(.inl .r2b, false), [0, 1, 2], true, 8⟩, ⟨(.inl .r3b, false), [0, 2, 3], false, 5⟩, ⟨(.inl .r3c, true), [0, 2], false, 6⟩, ⟨(.inl .r3c, false), [0, 2], true, 7⟩,
      ⟨(.inl .r2d, false), [0, 2], false, 6⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 10⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 9⟩, ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 8⟩,
      ⟨(.inr .k22, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r3b, false), [0, 1, 3], true, 6⟩, ⟨(.inl .r2b, false), [2, 3, 0], true, 8⟩,
      ⟨(.inl .r2b, false), [2, 3, 1], true, 9⟩, ⟨(.inl .r3c, true), [2, 3], false, 10⟩, ⟨(.inl .r3c, false), [2, 3], true, 11⟩, ⟨(.inl .r1a, false), [2, 3], true, 12⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 10⟩, ⟨(.inl .r2d, false), [2, 3], false, 11⟩, ⟨(.inl .r1b, false), [2], true, 10⟩, ⟨(.inl .r1b, false), [3], true, 10⟩,
      ⟨(.inl .r2b, false), [1, 3, 0], true, 7⟩, ⟨(.inl .r3c, true), [1, 3], false, 8⟩, ⟨(.inl .r1a, false), [1, 3], true, 9⟩, ⟨(.inl .r2d, false), [1, 3], false, 8⟩,
      ⟨(.inl .r1b, false), [3], true, 9⟩, ⟨(.inl .r2d, false), [2, 5], false, 9⟩, ⟨(.inl .r2d, false), [0, 1], true, 7⟩, ⟨(.inl .r2d, false), [0, 2], true, 8⟩,
      ⟨(.inl .r2d, false), [0, 5], true, 9⟩, ⟨(.inl .r1b, false), [0], true, 10⟩, ⟨(.inl .r2d, false), [1, 2], true, 7⟩, ⟨(.inl .r2d, false), [1, 5], true, 8⟩,
      ⟨(.inl .r1a, false), [0, 2], false, 9⟩, ⟨(.inl .r2b, false), [0, 2, 5], false, 8⟩, ⟨(.inl .r3c, true), [0, 2], true, 7⟩, ⟨(.inl .r3a, true), [0, 2, 3], true, 6⟩,
      ⟨(.inl .r2e, false), [1, 0, 2, 4, 5], true, 11⟩, ⟨(.inl .r4a, false), [0, 2, 4, 5], true, 10⟩, ⟨(.inr .k32, false), [0, 2, 4, 5], true, 8⟩, ⟨(.inl .r3e, false), [0, 2, 3, 4, 5], true, 7⟩,
      ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 6⟩, ⟨(.inl .r3b, true), [0, 2, 3], true, 7⟩, ⟨(.inl .r3a, false), [0, 3, 5], true, 8⟩, ⟨(.inl .r3b, false), [0, 3, 5], true, 8⟩,
      ⟨(.inl .r2a, false), [0, 5, 2, 3], false, 7⟩, ⟨(.inl .r3b, true), [2, 3, 5], true, 8⟩, ⟨(.inl .r3a, true), [2, 4, 5], true, 9⟩, ⟨(.inl .r2a, false), [2, 4, 3, 5], false, 8⟩,
      ⟨(.inl .r3c, true), [2, 5], true, 14⟩, ⟨(.inl .r2b, false), [2, 5, 4], false, 13⟩, ⟨(.inl .r3c, false), [2, 5], false, 12⟩, ⟨(.inl .r2b, false), [2, 5, 0], false, 11⟩,
      ⟨(.inl .r3b, true), [2, 4, 5], false, 10⟩, ⟨(.inl .r2a, false), [2, 4, 3, 5], false, 9⟩, ⟨(.inl .r1a, false), [2, 4], true, 8⟩, ⟨(.inl .r2d, false), [4, 5], false, 11⟩,
      ⟨(.inl .r2d, false), [2, 5], false, 12⟩, ⟨(.inl .r2d, false), [2, 4], false, 11⟩, ⟨(.inl .r2d, false), [2, 4], true, 11⟩, ⟨(.inl .r2d, false), [2, 5], true, 12⟩,
      ⟨(.inl .r1b, false), [2], true, 13⟩, ⟨(.inl .r1b, false), [5], true, 12⟩, ⟨(.inl .r2d, false), [1, 4], false, 11⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 4⟩,
      ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 5⟩]
  | false, true, false, true =>
    [⟨(.inl .r1b, false), [2], false, 3⟩, ⟨(.inl .r1c, false), [0, 2, 4, 5], false, 4⟩, ⟨(.inl .r1b, false), [2], false, 0⟩, ⟨(.inl .r1a, false), [1, 3], false, 0⟩,
      ⟨(.inl .r2b, false), [1, 3, 2], true, 1⟩, ⟨(.inl .r1a, false), [0, 1], false, 2⟩, ⟨(.inl .r2b, false), [0, 1, 2], false, 1⟩, ⟨(.inl .r3b, false), [0, 1, 3], true, 0⟩,
      ⟨(.inl .r2e, false), [2, 0, 1, 4, 5], true, 5⟩, ⟨(.inl .r3e, false), [0, 1, 3, 4, 5], true, 4⟩, ⟨(.inl .r3d, false), [0, 1, 3, 4, 5], true, 3⟩, ⟨(.inl .r2d, false), [1, 2], false, 6⟩,
      ⟨(.inl .r3a, true), [0, 1, 3], false, 4⟩, ⟨(.inl .r3c, false), [0, 1], true, 5⟩, ⟨(.inl .r2b, false), [0, 1, 2], true, 6⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 7⟩,
      ⟨(.inr .k22, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r3b, false), [1, 2, 3], false, 5⟩, ⟨(.inl .r3a, false), [1, 2, 3], false, 5⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 6⟩, ⟨(.inl .r2b, false), [0, 1, 2], false, 7⟩, ⟨(.inl .r3c, true), [0, 1], true, 6⟩, ⟨(.inl .r3b, false), [0, 1, 2], true, 5⟩,
      ⟨(.inl .r3c, false), [2, 3], false, 8⟩, ⟨(.inl .r2b, false), [2, 3, 0], false, 7⟩, ⟨(.inl .r2d, false), [0, 3], false, 9⟩, ⟨(.inl .r1b, false), [0], true, 8⟩,
      ⟨(.inl .r2d, false), [1, 3], false, 8⟩, ⟨(.inl .r2d, false), [2, 3], false, 9⟩, ⟨(.inl .r1b, false), [3], true, 10⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 9⟩,
      ⟨(.inl .r3c, false), [1, 3], false, 8⟩, ⟨(.inl .r3b, true), [1, 2, 3], false, 7⟩, ⟨(.inl .r1a, false), [1, 2], true, 6⟩, ⟨(.inl .r2d, false), [2, 3], false, 7⟩,
      ⟨(.inl .r2d, false), [1, 3], false, 8⟩, ⟨(.inl .r2d, false), [1, 2], false, 7⟩, ⟨(.inl .r1b, false), [3], true, 9⟩, ⟨(.inl .r1b, false), [2], true, 8⟩,
      ⟨(.inl .r2e, false), [1, 0, 2, 4, 5], true, 7⟩, ⟨(.inl .r3e, false), [0, 2, 3, 4, 5], true, 6⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 5⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 3⟩,
      ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 4⟩]
  | false, true, true, false =>
    [⟨(.inl .r1b, false), [0], false, 3⟩, ⟨(.inl .r1c, false), [0, 2, 4, 5], false, 4⟩, ⟨(.inl .r1b, false), [2], false, 0⟩, ⟨(.inl .r1a, false), [1, 2], false, 0⟩,
      ⟨(.inl .r3c, false), [1, 2], true, 1⟩, ⟨(.inl .r1a, false), [0, 1], false, 2⟩, ⟨(.inl .r3c, true), [0, 1], true, 1⟩, ⟨(.inl .r3b, false), [0, 1, 2], true, 0⟩,
      ⟨(.inl .r1a, false), [2, 3], false, 2⟩, ⟨(.inl .r2b, false), [2, 3, 0], true, 3⟩, ⟨(.inl .r2e, false), [2, 0, 1, 4, 5], true, 7⟩, ⟨(.inl .r3e, false), [0, 1, 2, 4, 5], true, 6⟩,
      ⟨(.inl .r3d, false), [0, 1, 2, 4, 5], true, 5⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], false, 5⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 6⟩,
      ⟨(.inl .r2d, false), [1, 2], false, 8⟩, ⟨(.inl .r3a, true), [0, 1, 3], false, 5⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inl .r3c, false), [0, 1], true, 7⟩,
      ⟨(.inl .r2b, false), [0, 1, 2], true, 8⟩, ⟨(.inl .r3b, false), [0, 2, 3], false, 5⟩, ⟨(.inl .r3c, true), [0, 2], false, 6⟩, ⟨(.inl .r3c, false), [0, 2], true, 7⟩,
      ⟨(.inl .r2d, false), [0, 2], false, 6⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 9⟩, ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 8⟩, ⟨(.inr .k22, false), [0, 1, 2, 3], true, 6⟩,
      ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r3b, false), [0, 1, 3], true, 6⟩, ⟨(.inl .r2b, false), [2, 3, 0], true, 8⟩, ⟨(.inl .r2b, false), [2, 3, 1], true, 9⟩,
      ⟨(.inl .r3c, true), [2, 3], false, 10⟩, ⟨(.inl .r3c, false), [2, 3], true, 11⟩, ⟨(.inl .r1a, false), [2, 3], true, 12⟩, ⟨(.inl .r2d, false), [2, 3], false, 10⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 11⟩, ⟨(.inl .r1b, false), [2], true, 10⟩, ⟨(.inl .r1b, false), [3], true, 10⟩, ⟨(.inl .r2b, false), [1, 3, 0], true, 7⟩,
      ⟨(.inl .r3c, true), [1, 3], false, 8⟩, ⟨(.inl .r1a, false), [1, 3], true, 9⟩, ⟨(.inl .r2d, false), [1, 3], false, 8⟩, ⟨(.inl .r1b, false), [3], true, 9⟩,
      ⟨(.inl .r2d, false), [0, 1], false, 8⟩, ⟨(.inl .r1b, false), [0], true, 7⟩, ⟨(.inl .r1a, false), [0, 2], false, 6⟩, ⟨(.inl .r3a, false), [0, 2, 3], true, 7⟩,
      ⟨(.inl .r2e, false), [1, 0, 2, 4, 5], true, 9⟩, ⟨(.inl .r4a, false), [0, 2, 4, 5], true, 8⟩, ⟨(.inl .r3e, false), [0, 2, 3, 4, 5], true, 7⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 6⟩,
      ⟨(.inl .r3a, false), [2, 3, 5], true, 8⟩, ⟨(.inl .r3b, false), [2, 3, 5], true, 8⟩, ⟨(.inl .r2d, false), [1, 5], false, 11⟩, ⟨(.inl .r2d, false), [1, 2], false, 10⟩,
      ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 5⟩]
  | true, false, false, true =>
    [⟨(.inl .r1b, false), [2], false, 3⟩, ⟨(.inl .r1c, false), [0, 2, 4, 5], false, 4⟩, ⟨(.inl .r1b, false), [3], false, 0⟩, ⟨(.inl .r1a, false), [1, 2], false, 0⟩,
      ⟨(.inl .r2b, false), [1, 2, 3], true, 1⟩, ⟨(.inl .r1a, false), [0, 1], false, 2⟩, ⟨(.inl .r2b, false), [0, 1, 3], false, 1⟩, ⟨(.inl .r3b, false), [0, 1, 2], true, 0⟩,
      ⟨(.inl .r1a, false), [2, 3], false, 2⟩, ⟨(.inl .r3c, false), [2, 3], true, 3⟩, ⟨(.inl .r2e, false), [3, 0, 1, 4, 5], true, 7⟩, ⟨(.inl .r3e, false), [0, 1, 2, 4, 5], true, 6⟩,
      ⟨(.inl .r3d, false), [0, 1, 2, 4, 5], true, 5⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], false, 5⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 6⟩,
      ⟨(.inl .r2d, false), [0, 3], false, 8⟩, ⟨(.inl .r3a, true), [0, 1, 3], false, 5⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inl .r3c, true), [0, 1], false, 7⟩,
      ⟨(.inl .r2b, false), [0, 1, 3], true, 8⟩, ⟨(.inl .r3b, false), [0, 2, 3], false, 5⟩, ⟨(.inl .r2b, false), [0, 2, 1], true, 6⟩, ⟨(.inl .r2b, false), [0, 2, 3], true, 7⟩,
      ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 9⟩, ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 8⟩, ⟨(.inr .k21, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 5⟩,
      ⟨(.inl .r3b, false), [0, 1, 3], true, 6⟩, ⟨(.inl .r1a, false), [2, 3], true, 8⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 7⟩, ⟨(.inl .r3c, false), [1, 3], true, 8⟩,
      ⟨(.inl .r2d, false), [1, 2], false, 7⟩, ⟨(.inl .r1a, false), [1, 3], true, 9⟩, ⟨(.inl .r2d, false), [1, 2], false, 8⟩, ⟨(.inl .r1b, false), [1], true, 7⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 8⟩, ⟨(.inl .r1b, false), [2], true, 7⟩, ⟨(.inl .r1a, false), [0, 2], false, 6⟩, ⟨(.inl .r3a, false), [0, 2, 3], true, 7⟩,
      ⟨(.inl .r2e, false), [3, 0, 2, 4, 5], true, 9⟩, ⟨(.inl .r4a, false), [0, 2, 4, 5], true, 8⟩, ⟨(.inl .r3e, false), [0, 2, 3, 4, 5], true, 7⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 6⟩,
      ⟨(.inl .r3a, false), [2, 3, 5], true, 8⟩, ⟨(.inl .r3b, false), [2, 3, 5], true, 8⟩, ⟨(.inl .r2d, false), [3, 5], false, 11⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 4⟩,
      ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 5⟩]
  | true, false, true, false =>
    [⟨(.inl .r1b, false), [0], false, 3⟩, ⟨(.inl .r1c, false), [0, 2, 4, 5], false, 4⟩, ⟨(.inl .r1b, false), [3], false, 0⟩, ⟨(.inl .r1a, false), [1, 3], false, 0⟩,
      ⟨(.inl .r3c, false), [1, 3], true, 1⟩, ⟨(.inl .r1a, false), [0, 1], false, 2⟩, ⟨(.inl .r3c, true), [0, 1], true, 1⟩, ⟨(.inl .r3b, false), [0, 1, 3], true, 0⟩,
      ⟨(.inl .r2e, false), [3, 0, 1, 4, 5], true, 5⟩, ⟨(.inl .r3e, false), [0, 1, 3, 4, 5], true, 4⟩, ⟨(.inl .r3d, false), [0, 1, 3, 4, 5], true, 3⟩, ⟨(.inl .r2d, false), [0, 3], false, 6⟩,
      ⟨(.inl .r3a, true), [0, 1, 3], false, 4⟩, ⟨(.inl .r3c, true), [0, 1], false, 5⟩, ⟨(.inl .r2b, false), [0, 1, 3], true, 6⟩, ⟨(.inl .r2b, false), [0, 3, 1], true, 4⟩,
      ⟨(.inl .r3c, false), [0, 3], true, 5⟩, ⟨(.inl .r2d, false), [0, 1], false, 4⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 6⟩,
      ⟨(.inr .k12, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r2b, false), [1, 3, 0], true, 6⟩, ⟨(.inl .r3c, true), [1, 3], false, 7⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 8⟩,
      ⟨(.inl .r3c, false), [1, 3], true, 9⟩, ⟨(.inl .r1a, false), [1, 3], true, 10⟩, ⟨(.inl .r2d, false), [2, 3], false, 7⟩, ⟨(.inl .r2d, false), [1, 3], false, 8⟩,
      ⟨(.inl .r2d, false), [1, 2], false, 7⟩, ⟨(.inl .r2d, false), [2, 3], true, 8⟩, ⟨(.inl .r3c, false), [2, 3], false, 9⟩, ⟨(.inl .r3c, true), [2, 3], true, 8⟩,
      ⟨(.inl .r2b, false), [2, 3, 1], false, 7⟩, ⟨(.inl .r2b, false), [2, 3, 0], false, 6⟩, ⟨(.inl .r2d, false), [1, 2], true, 8⟩, ⟨(.inl .r2d, false), [1, 3], true, 9⟩,
      ⟨(.inl .r2d, false), [2, 3], true, 8⟩, ⟨(.inl .r3c, false), [1, 3], false, 10⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 9⟩, ⟨(.inl .r3c, true), [1, 3], true, 8⟩,
      ⟨(.inl .r2b, false), [1, 3, 0], false, 7⟩, ⟨(.inl .r3b, true), [1, 2, 3], false, 6⟩, ⟨(.inl .r2d, false), [1, 2], true, 9⟩, ⟨(.inl .r2d, false), [1, 3], true, 10⟩,
      ⟨(.inl .r1b, false), [1], true, 11⟩, ⟨(.inl .r2d, false), [2, 3], false, 10⟩, ⟨(.inl .r1b, false), [2], true, 9⟩, ⟨(.inl .r3b, true), [1, 2, 3], true, 6⟩,
      ⟨(.inl .r2b, false), [1, 3, 0], true, 7⟩, ⟨(.inl .r3c, false), [1, 3], true, 8⟩, ⟨(.inl .r1a, false), [1, 3], true, 9⟩, ⟨(.inl .r1b, false), [1], true, 8⟩,
      ⟨(.inl .r2d, false), [0, 3], false, 8⟩, ⟨(.inl .r1b, false), [0], true, 7⟩, ⟨(.inl .r2e, false), [3, 0, 2, 4, 5], true, 7⟩, ⟨(.inl .r3e, false), [0, 2, 3, 4, 5], true, 6⟩,
      ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 5⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 4⟩]
  | true, true, false, false =>
    [⟨(.inl .r1c, false), [0, 2, 4, 5], false, 4⟩, ⟨(.inl .r1b, false), [3], false, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩, ⟨(.inl .r2b, false), [0, 1, 3], true, 1⟩,
      ⟨(.inl .r1a, false), [1, 2], false, 1⟩, ⟨(.inl .r2b, false), [1, 2, 3], true, 2⟩, ⟨(.inl .r3a, true), [0, 1, 2], false, 0⟩, ⟨(.inl .r2b, false), [0, 1, 3], true, 1⟩,
      ⟨(.inl .r1a, false), [2, 3], false, 1⟩, ⟨(.inl .r3c, false), [2, 3], true, 2⟩, ⟨(.inl .r1a, false), [4, 5], false, 2⟩, ⟨(.inl .r2b, false), [4, 5, 2], true, 3⟩,
      ⟨(.inl .r2e, false), [3, 0, 1, 4, 5], true, 9⟩, ⟨(.inl .r4a, false), [0, 1, 4, 5], true, 8⟩, ⟨(.inl .r3e, false), [0, 1, 2, 4, 5], true, 7⟩, ⟨(.inl .r3d, false), [0, 1, 2, 4, 5], true, 6⟩,
      ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 5⟩, ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 4⟩, ⟨(.inl .r3b, false), [2, 3, 5], true, 5⟩, ⟨(.inl .r2a, false), [0, 1, 3, 5], false, 6⟩,
      ⟨(.inl .r2a, false), [0, 1, 2, 5], false, 5⟩, ⟨(.inl .r2a, false), [1, 2, 3, 5], false, 7⟩, ⟨(.inl .r3b, false), [1, 2, 5], true, 6⟩, ⟨(.inl .r3b, false), [2, 3, 5], false, 7⟩,
      ⟨(.inl .r2a, false), [1, 5, 2, 3], false, 8⟩, ⟨(.inl .r3b, true), [1, 3, 5], false, 7⟩, ⟨(.inl .r3a, true), [1, 3, 5], false, 7⟩, ⟨(.inl .r1a, false), [1, 5], true, 6⟩,
      ⟨(.inl .r2d, false), [3, 5], false, 9⟩, ⟨(.inl .r2d, false), [0, 5], false, 10⟩, ⟨(.inl .r2d, false), [0, 3], false, 9⟩, ⟨(.inl .r2d, false), [0, 1], false, 8⟩,
      ⟨(.inl .r2d, false), [1, 3], true, 9⟩, ⟨(.inl .r2d, false), [1, 5], true, 10⟩, ⟨(.inl .r1b, false), [1], true, 11⟩, ⟨(.inl .r3a, true), [0, 1, 3], false, 5⟩,
      ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inl .r3c, true), [0, 1], false, 7⟩, ⟨(.inl .r2b, false), [0, 1, 3], true, 8⟩, ⟨(.inl .r3b, false), [0, 2, 3], false, 5⟩,
      ⟨(.inl .r2b, false), [0, 2, 1], true, 6⟩, ⟨(.inl .r2b, false), [0, 2, 3], true, 7⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 10⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 9⟩,
      ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 8⟩, ⟨(.inr .k21, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r3b, false), [0, 1, 3], true, 6⟩,
      ⟨(.inl .r1a, false), [2, 3], true, 8⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 7⟩, ⟨(.inl .r3c, false), [1, 3], true, 8⟩, ⟨(.inl .r2d, false), [1, 2], false, 7⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 9⟩, ⟨(.inl .r2d, false), [1, 2], false, 8⟩, ⟨(.inl .r1b, false), [1], true, 7⟩, ⟨(.inl .r2d, false), [3, 5], true, 8⟩,
      ⟨(.inl .r1a, false), [0, 2], false, 9⟩, ⟨(.inl .r2b, false), [0, 2, 5], false, 8⟩, ⟨(.inl .r3c, true), [0, 2], true, 7⟩, ⟨(.inl .r3a, true), [0, 2, 3], true, 6⟩,
      ⟨(.inl .r2e, false), [3, 0, 2, 4, 5], true, 11⟩, ⟨(.inl .r4a, false), [0, 2, 4, 5], true, 10⟩, ⟨(.inr .k32, false), [0, 2, 4, 5], true, 8⟩, ⟨(.inl .r3e, false), [0, 2, 3, 4, 5], true, 7⟩,
      ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 6⟩, ⟨(.inl .r3b, true), [0, 2, 3], true, 7⟩, ⟨(.inl .r3a, false), [0, 3, 5], true, 8⟩, ⟨(.inl .r3b, false), [0, 3, 5], true, 8⟩,
      ⟨(.inl .r2a, false), [0, 5, 2, 3], false, 7⟩, ⟨(.inl .r3b, true), [2, 3, 5], true, 8⟩, ⟨(.inl .r3a, true), [2, 4, 5], true, 9⟩, ⟨(.inl .r2a, false), [2, 4, 3, 5], false, 8⟩,
      ⟨(.inl .r3c, true), [2, 5], true, 14⟩, ⟨(.inl .r2b, false), [2, 5, 4], false, 13⟩, ⟨(.inl .r3c, false), [2, 5], false, 12⟩, ⟨(.inl .r2b, false), [2, 5, 0], false, 11⟩,
      ⟨(.inl .r3b, true), [2, 4, 5], false, 10⟩, ⟨(.inl .r2a, false), [2, 4, 3, 5], false, 9⟩, ⟨(.inl .r1a, false), [2, 4], true, 8⟩, ⟨(.inl .r2d, false), [4, 5], false, 11⟩,
      ⟨(.inl .r2d, false), [2, 5], false, 12⟩, ⟨(.inl .r2d, false), [2, 4], false, 11⟩, ⟨(.inl .r2d, false), [2, 4], true, 11⟩, ⟨(.inl .r2d, false), [2, 5], true, 12⟩,
      ⟨(.inl .r1b, false), [2], true, 13⟩, ⟨(.inl .r1b, false), [5], true, 12⟩, ⟨(.inl .r2d, false), [3, 4], false, 11⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 4⟩,
      ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 5⟩]
  | true, true, true, true =>
    [⟨(.inl .r1b, false), [2], false, 4⟩, ⟨(.inl .r1b, false), [0], false, 4⟩, ⟨(.inl .r2d, false), [0, 2], true, 5⟩, ⟨(.inl .r2d, false), [0, 2], true, 4⟩,
      ⟨(.inl .r1c, false), [0, 2, 4, 5], false, 6⟩, ⟨(.inl .r1b, false), [3], false, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩, ⟨(.inl .r2b, false), [0, 1, 3], true, 1⟩,
      ⟨(.inl .r1a, false), [1, 3], false, 1⟩, ⟨(.inl .r3c, false), [1, 3], true, 2⟩, ⟨(.inl .r3a, true), [0, 1, 3], false, 0⟩, ⟨(.inl .r3c, false), [0, 1], true, 1⟩,
      ⟨(.inl .r1a, false), [4, 5], false, 1⟩, ⟨(.inl .r2b, false), [4, 5, 0], true, 2⟩, ⟨(.inl .r2e, false), [3, 0, 1, 4, 5], true, 7⟩, ⟨(.inl .r4a, false), [0, 1, 4, 5], true, 6⟩,
      ⟨(.inl .r3e, false), [0, 1, 3, 4, 5], true, 5⟩, ⟨(.inl .r3d, false), [0, 1, 3, 4, 5], true, 4⟩, ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 3⟩, ⟨(.inl .r2a, false), [0, 1, 3, 5], false, 4⟩,
      ⟨(.inl .r3b, false), [1, 3, 5], true, 5⟩, ⟨(.inl .r3b, false), [1, 3, 5], false, 5⟩, ⟨(.inl .r3a, false), [1, 3, 5], false, 5⟩, ⟨(.inl .r1a, false), [1, 5], true, 6⟩,
      ⟨(.inl .r2d, false), [3, 5], false, 7⟩, ⟨(.inl .r2d, false), [0, 5], false, 8⟩, ⟨(.inl .r2d, false), [0, 3], false, 7⟩, ⟨(.inl .r2d, false), [0, 1], false, 6⟩,
      ⟨(.inl .r2d, false), [1, 3], true, 7⟩, ⟨(.inl .r2d, false), [1, 5], true, 8⟩, ⟨(.inl .r1b, false), [1], true, 9⟩, ⟨(.inl .r3a, true), [0, 1, 3], false, 4⟩,
      ⟨(.inl .r3c, true), [0, 1], false, 5⟩, ⟨(.inl .r2b, false), [0, 1, 3], true, 6⟩, ⟨(.inl .r2b, false), [0, 3, 1], true, 4⟩, ⟨(.inl .r3c, false), [0, 3], true, 5⟩,
      ⟨(.inl .r2d, false), [0, 1], false, 4⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 8⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 6⟩,
      ⟨(.inr .k12, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r2b, false), [1, 3, 0], true, 6⟩, ⟨(.inl .r3c, true), [1, 3], false, 7⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 8⟩,
      ⟨(.inl .r3c, false), [1, 3], true, 9⟩, ⟨(.inl .r1a, false), [1, 3], true, 10⟩, ⟨(.inl .r2d, false), [2, 3], false, 7⟩, ⟨(.inl .r2d, false), [1, 3], false, 8⟩,
      ⟨(.inl .r2d, false), [1, 2], false, 7⟩, ⟨(.inl .r2d, false), [2, 3], true, 8⟩, ⟨(.inl .r3c, false), [2, 3], false, 9⟩, ⟨(.inl .r3c, true), [2, 3], true, 8⟩,
      ⟨(.inl .r2b, false), [2, 3, 1], false, 7⟩, ⟨(.inl .r2b, false), [2, 3, 0], false, 6⟩, ⟨(.inl .r2d, false), [1, 2], true, 8⟩, ⟨(.inl .r2d, false), [1, 3], true, 9⟩,
      ⟨(.inl .r2d, false), [2, 3], true, 8⟩, ⟨(.inl .r3c, false), [1, 3], false, 10⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 9⟩, ⟨(.inl .r3c, true), [1, 3], true, 8⟩,
      ⟨(.inl .r2b, false), [1, 3, 0], false, 7⟩, ⟨(.inl .r3b, true), [1, 2, 3], false, 6⟩, ⟨(.inl .r2d, false), [1, 2], true, 9⟩, ⟨(.inl .r2d, false), [1, 3], true, 10⟩,
      ⟨(.inl .r1b, false), [1], true, 11⟩, ⟨(.inl .r2d, false), [2, 3], false, 10⟩, ⟨(.inl .r1b, false), [2], true, 9⟩, ⟨(.inl .r3b, true), [1, 2, 3], true, 6⟩,
      ⟨(.inl .r2b, false), [1, 3, 0], true, 7⟩, ⟨(.inl .r3c, false), [1, 3], true, 8⟩, ⟨(.inl .r1a, false), [1, 3], true, 9⟩, ⟨(.inl .r1b, false), [1], true, 8⟩,
      ⟨(.inl .r2d, false), [2, 5], false, 9⟩, ⟨(.inl .r2d, false), [2, 3], false, 8⟩, ⟨(.inl .r2d, false), [0, 2], true, 7⟩, ⟨(.inl .r2d, false), [0, 3], true, 8⟩,
      ⟨(.inl .r2d, false), [0, 5], true, 9⟩, ⟨(.inl .r1b, false), [0], true, 10⟩, ⟨(.inl .r2d, false), [3, 5], true, 8⟩, ⟨(.inl .r3c, true), [2, 3], false, 6⟩,
      ⟨(.inl .r2b, false), [2, 3, 5], true, 7⟩, ⟨(.inl .r2b, false), [0, 2, 3], true, 5⟩, ⟨(.inl .r2b, false), [0, 2, 5], true, 6⟩, ⟨(.inl .r2e, false), [3, 0, 2, 4, 5], true, 9⟩,
      ⟨(.inl .r3e, false), [0, 2, 3, 4, 5], true, 8⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 7⟩, ⟨(.inr .k21, false), [2, 3, 4, 5], true, 5⟩, ⟨(.inl .r2a, false), [0, 2, 4, 5], false, 7⟩,
      ⟨(.inl .r3b, false), [0, 2, 3], true, 6⟩, ⟨(.inl .r2a, false), [2, 3, 4, 5], false, 8⟩, ⟨(.inl .r1a, false), [2, 3], true, 7⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 3⟩,
      ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 4⟩]
  | _, _, _, _ => []

theorem chk323_0201 : ∀ x y p q : Bool, xor (xor (xor x y) p) q = false →
    checkD (Gen.k 0 1 4 5 (by decide) (by decide) (by decide) :: (negw x 0 ++ negw y 1) ++ [Gen.k 0 1 2 3 (by decide) (by decide) (by decide)])
      (X323_0201 x y p q ++ Gen.k 0 1 2 4 (by decide) (by decide) (by decide) :: Y323_0201 x y p q ++
        Gen.k 0 2 4 5 (by decide) (by decide) (by decide) :: (negw p 0 ++ negw q 2)) (S323_0201 x y p q) = true := by
  decide +kernel

theorem tag323_0201 : ∀ x y p q : Bool, ∀ g ∈ X323_0201 x y p q ++ Y323_0201 x y p q, g.tag ≠ 2 := by
  decide

/-- Subcase 3.2.3 with `{a,b} = {0,2}`, `{α,β} = {0,1}` (from `0`). -/
theorem rel323_0201 {a0 a1 a2 a3 c d : Fin n} (h1 : a0 < a1) (h2 : a1 < a2) (h3 : a2 < a3) (h4 : a3 < c) (h5 : c < d) (x y p q : Bool)
    (hpar : xor (xor (xor x y) p) q = false) :
    ∃ Xw Yw : List (Gen n), (∀ g ∈ Xw ++ Yw, g.tag ≠ 2 ∧ extent g ≤ d.val) ∧
      Derivable (Table1 n)
        (FreeMonoid.ofList (Gen.k a0 a1 c d h1 (h2.trans (h3.trans h4)) h5 :: (negw x a0 ++ negw y a1) ++
          [Gen.k a0 a1 a2 a3 h1 h2 h3]))
        (FreeMonoid.ofList (Xw ++ Gen.k a0 a1 a2 c h1 h2 (h3.trans h4) :: Yw ++
          Gen.k a0 a2 c d (h1.trans h2) (h3.trans h4) h5 :: (negw p a0 ++ negw q a2))) := by
  refine ⟨(X323_0201 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)),
    (Y323_0201 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)), ?_, ?_⟩
  · intro g hg
    rw [← List.map_append] at hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    refine ⟨by rw [tag_rename]; exact tag323_0201 x y p q g' hg', ?_⟩
    have := extent_rename_le (emb6 h1 h2 h3 h4 h5) g' 5 (extent_le_last g')
    rwa [emb6_5] at this
  · have hh := derivable_rename (emb6 h1 h2 h3 h4 h5) (checkD_sound (chk323_0201 x y p q hpar))
    rw [renW_ofList, renW_ofList] at hh
    convert hh using 2 <;>
      simp only [List.map_append, List.map_cons, List.map_nil, negw_rename, Gen.rename, emb6_0,
        emb6_1, emb6_2, emb6_3, emb6_4, emb6_5, List.cons_append, List.nil_append,
        List.append_assoc]

/-- `X` for `{a,b} = {0,2}`, `{α,β} = {2,3}`. -/
def X323_0223 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, true => [Gen.x 1 3 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 2]
  | false, false, true, false => [Gen.x 1 3 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 0]
  | false, true, false, false => [Gen.neg 1]
  | false, true, true, true => [Gen.x 0 1 (by decide), Gen.neg 0]
  | true, false, false, false => [Gen.x 1 2 (by decide), Gen.neg 2]
  | true, false, true, true => [Gen.x 0 1 (by decide), Gen.x 1 2 (by decide), Gen.neg 0]
  | true, true, false, true => [Gen.x 1 3 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 2]
  | true, true, true, false => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 0]
  | _, _, _, _ => []

/-- `Y` for `{a,b} = {0,2}`, `{α,β} = {2,3}`. -/
def Y323_0223 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, true => [Gen.x 0 3 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide)]
  | false, false, true, false => [Gen.x 0 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 3, Gen.neg 4]
  | false, true, false, false => [Gen.x 0 1 (by decide), Gen.x 2 3 (by decide)]
  | false, true, true, true => [Gen.x 0 1 (by decide), Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.neg 2, Gen.neg 5]
  | true, false, false, false => [Gen.x 0 2 (by decide), Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.neg 2, Gen.neg 5]
  | true, false, true, true => [Gen.x 0 2 (by decide), Gen.x 2 3 (by decide)]
  | true, true, false, true => [Gen.x 0 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 0, Gen.neg 4]
  | true, true, true, false => [Gen.x 0 3 (by decide), Gen.x 4 5 (by decide)]
  | _, _, _, _ => []

/-- The chains for `{a,b} = {0,2}`, `{α,β} = {2,3}`. -/
def S323_0223 : Bool → Bool → Bool → Bool → List (GStep ((Fam ⊕ MFam) × Bool) 6)
  | false, false, false, true =>
    [⟨(.inl .r1b, false), [2], false, 2⟩, ⟨(.inl .r1c, false), [0, 2, 4, 5], false, 3⟩, ⟨(.inl .r1b, false), [1], false, 0⟩, ⟨(.inl .r1a, false), [1, 2], false, 0⟩,
      ⟨(.inl .r3c, true), [1, 2], false, 1⟩, ⟨(.inl .r1a, false), [1, 3], false, 2⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 1⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 0⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [4, 5], false, 2⟩, ⟨(.inl .r2b, false), [4, 5, 2], true, 3⟩, ⟨(.inl .r2e, false), [1, 2, 3, 4, 5], true, 7⟩,
      ⟨(.inl .r3d, true), [1, 2, 3, 4, 5], false, 6⟩, ⟨(.inl .r4a, false), [1, 3, 4, 5], true, 5⟩, ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 4⟩, ⟨(.inl .r1a, false), [3, 5], true, 5⟩,
      ⟨(.inl .r2b, false), [1, 2, 5], false, 6⟩, ⟨(.inl .r2b, false), [1, 2, 3], false, 5⟩, ⟨(.inl .r2d, false), [1, 5], false, 7⟩, ⟨(.inl .r2d, false), [1, 3], false, 6⟩,
      ⟨(.inl .r3c, true), [1, 2], false, 5⟩, ⟨(.inl .r2b, false), [1, 2, 3], true, 6⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 8⟩, ⟨(.inr .ksym2, false), [0, 1, 2, 3], true, 7⟩,
      ⟨(.inr .k11, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r3a, true), [1, 2, 3], true, 7⟩, ⟨(.inl .r2d, false), [2, 5], false, 9⟩, ⟨(.inl .r3b, false), [0, 1, 2], false, 6⟩,
      ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inl .r2b, false), [0, 1, 2], true, 8⟩, ⟨(.inl .r2b, false), [0, 1, 5], true, 9⟩, ⟨(.inl .r3c, true), [2, 3], false, 7⟩,
      ⟨(.inl .r2b, false), [2, 3, 5], true, 8⟩, ⟨(.inl .r2b, false), [1, 2, 3], true, 6⟩, ⟨(.inl .r2b, false), [1, 2, 5], true, 7⟩, ⟨(.inl .r3d, false), [0, 1, 2, 4, 5], true, 10⟩,
      ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 9⟩, ⟨(.inl .r3d, false), [1, 2, 3, 4, 5], true, 8⟩, ⟨(.inr .k21, false), [2, 3, 4, 5], true, 6⟩, ⟨(.inl .r2a, false), [1, 2, 4, 5], false, 8⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], true, 7⟩, ⟨(.inl .r2a, false), [2, 3, 4, 5], false, 9⟩, ⟨(.inl .r1a, false), [2, 3], true, 8⟩, ⟨(.inl .r2a, false), [0, 1, 4, 5], false, 8⟩,
      ⟨(.inl .r3b, false), [0, 1, 3], true, 7⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 5⟩]
  | false, false, true, false =>
    [⟨(.inl .r1b, false), [0], false, 2⟩, ⟨(.inl .r1c, false), [0, 2, 4, 5], false, 3⟩, ⟨(.inl .r1b, false), [0], false, 0⟩, ⟨(.inl .r1a, false), [1, 2], false, 0⟩,
      ⟨(.inl .r2b, false), [1, 2, 0], true, 1⟩, ⟨(.inl .r1a, false), [1, 3], false, 2⟩, ⟨(.inl .r2b, false), [1, 3, 0], false, 1⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 0⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [4, 5], false, 2⟩, ⟨(.inl .r2b, false), [4, 5, 0], true, 3⟩, ⟨(.inl .r2e, false), [0, 2, 3, 4, 5], true, 7⟩,
      ⟨(.inl .r3d, true), [1, 2, 3, 4, 5], false, 6⟩, ⟨(.inl .r4a, false), [1, 3, 4, 5], true, 5⟩, ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 4⟩, ⟨(.inl .r1a, false), [3, 5], true, 5⟩,
      ⟨(.inl .r2b, false), [1, 2, 5], false, 6⟩, ⟨(.inl .r2b, false), [1, 2, 3], false, 5⟩, ⟨(.inl .r2d, false), [0, 5], false, 7⟩, ⟨(.inl .r2d, false), [0, 3], false, 6⟩,
      ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 8⟩, ⟨(.inr .k32, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inr .ksym2, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r2a, false), [0, 3, 1, 2], false, 6⟩,
      ⟨(.inl .r1a, false), [1, 2], true, 7⟩, ⟨(.inl .r2d, false), [0, 5], false, 11⟩, ⟨(.inl .r2d, false), [0, 3], false, 10⟩, ⟨(.inl .r2d, false), [0, 2], false, 9⟩,
      ⟨(.inl .r2d, false), [0, 1], false, 8⟩, ⟨(.inl .r1b, false), [0], true, 7⟩, ⟨(.inl .r2d, false), [1, 2], true, 7⟩, ⟨(.inl .r2d, false), [1, 3], true, 8⟩,
      ⟨(.inl .r2d, false), [1, 5], true, 9⟩, ⟨(.inl .r2d, false), [3, 5], true, 8⟩, ⟨(.inl .r1a, false), [0, 2], false, 9⟩, ⟨(.inl .r2b, false), [0, 2, 5], false, 8⟩,
      ⟨(.inl .r3c, true), [0, 2], true, 7⟩, ⟨(.inl .r3a, true), [0, 2, 3], true, 6⟩, ⟨(.inl .r2e, false), [1, 0, 2, 4, 5], true, 12⟩, ⟨(.inl .r2e, false), [3, 0, 2, 4, 5], true, 11⟩,
      ⟨(.inl .r4a, false), [0, 2, 4, 5], true, 10⟩, ⟨(.inr .k32, false), [0, 2, 4, 5], true, 8⟩, ⟨(.inl .r3e, false), [0, 2, 3, 4, 5], true, 7⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 6⟩,
      ⟨(.inl .r3b, true), [0, 2, 3], true, 7⟩, ⟨(.inl .r3a, false), [0, 3, 5], true, 8⟩, ⟨(.inl .r3b, false), [0, 3, 5], true, 8⟩, ⟨(.inl .r2a, false), [0, 5, 2, 3], false, 7⟩,
      ⟨(.inl .r3b, true), [2, 3, 5], true, 8⟩, ⟨(.inl .r3a, true), [2, 4, 5], true, 9⟩, ⟨(.inl .r2a, false), [2, 4, 3, 5], false, 8⟩, ⟨(.inl .r3c, true), [2, 5], true, 14⟩,
      ⟨(.inl .r2b, false), [2, 5, 4], false, 13⟩, ⟨(.inl .r3c, false), [2, 5], false, 12⟩, ⟨(.inl .r2b, false), [2, 5, 0], false, 11⟩, ⟨(.inl .r3b, true), [2, 4, 5], false, 10⟩,
      ⟨(.inl .r2a, false), [2, 4, 3, 5], false, 9⟩, ⟨(.inl .r1a, false), [2, 4], true, 8⟩, ⟨(.inl .r2d, false), [4, 5], false, 11⟩, ⟨(.inl .r2d, false), [2, 5], false, 12⟩,
      ⟨(.inl .r2d, false), [2, 4], false, 11⟩, ⟨(.inl .r2d, false), [2, 4], true, 11⟩, ⟨(.inl .r2d, false), [2, 5], true, 12⟩, ⟨(.inl .r1b, false), [2], true, 13⟩,
      ⟨(.inl .r1b, false), [5], true, 12⟩, ⟨(.inl .r2d, false), [3, 4], false, 11⟩, ⟨(.inl .r2d, false), [1, 4], false, 12⟩, ⟨(.inl .r2d, false), [1, 3], false, 11⟩,
      ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 5⟩]
  | false, true, false, false =>
    [⟨(.inl .r1c, false), [0, 2, 4, 5], false, 3⟩, ⟨(.inl .r1b, false), [1], false, 0⟩, ⟨(.inl .r2e, false), [1, 2, 3, 4, 5], true, 1⟩, ⟨(.inr .k21, false), [0, 1, 2, 3], true, 2⟩,
      ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 3⟩, ⟨(.inl .r3d, false), [0, 1, 2, 4, 5], true, 4⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], false, 4⟩,
      ⟨(.inl .r5a, false), [0, 1, 2, 3, 4, 5], true, 2⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 1⟩]
  | false, true, true, true =>
    [⟨(.inl .r1b, false), [2], false, 3⟩, ⟨(.inl .r1b, false), [0], false, 3⟩, ⟨(.inl .r2d, false), [0, 2], true, 4⟩, ⟨(.inl .r2d, false), [0, 2], true, 3⟩,
      ⟨(.inl .r1c, false), [0, 2, 4, 5], false, 5⟩, ⟨(.inl .r1b, false), [1], false, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩, ⟨(.inl .r3c, false), [0, 1], true, 1⟩,
      ⟨(.inl .r2e, false), [1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r2c, false), [0, 1, 2, 3, 4, 5], true, 2⟩, ⟨(.inl .r3c, false), [0, 1], true, 3⟩, ⟨(.inl .r2b, false), [0, 1, 3], true, 4⟩,
      ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inr .k32, false), [0, 1, 2, 3], true, 3⟩, ⟨(.inl .r2d, false), [1, 2], true, 7⟩, ⟨(.inl .r2d, false), [1, 3], true, 8⟩,
      ⟨(.inl .r2d, false), [2, 3], true, 7⟩, ⟨(.inl .r3c, false), [1, 3], false, 9⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 8⟩, ⟨(.inl .r3c, true), [1, 3], true, 7⟩,
      ⟨(.inl .r2b, false), [1, 3, 0], false, 6⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 5⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 5⟩, ⟨(.inl .r2d, false), [1, 2], true, 8⟩,
      ⟨(.inl .r2d, false), [1, 3], true, 9⟩, ⟨(.inl .r1b, false), [1], true, 10⟩, ⟨(.inl .r1b, false), [3], true, 9⟩, ⟨(.inl .r1b, false), [2], true, 8⟩,
      ⟨(.inl .r1b, false), [0], true, 7⟩, ⟨(.inl .r3b, false), [0, 1, 3], false, 4⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r3b, false), [1, 2, 3], false, 4⟩,
      ⟨(.inl .r3d, false), [0, 1, 2, 4, 5], true, 6⟩, ⟨(.inl .r4a, false), [1, 2, 4, 5], true, 5⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r3a, false), [2, 3, 5], true, 5⟩,
      ⟨(.inl .r3b, false), [2, 3, 5], true, 5⟩, ⟨(.inl .r2b, false), [0, 1, 5], false, 8⟩, ⟨(.inl .r2b, false), [0, 1, 2], false, 7⟩, ⟨(.inl .r2a, false), [0, 1, 3, 5], false, 6⟩,
      ⟨(.inl .r2a, false), [0, 1, 2, 5], false, 5⟩, ⟨(.inl .r5a, false), [0, 1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 2⟩]
  | true, false, false, false =>
    [⟨(.inl .r1c, false), [0, 2, 4, 5], false, 3⟩, ⟨(.inl .r1b, false), [1], false, 0⟩, ⟨(.inl .r1a, false), [1, 2], false, 0⟩, ⟨(.inl .r3c, true), [1, 2], false, 1⟩,
      ⟨(.inl .r2e, false), [1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r3d, true), [1, 2, 3, 4, 5], false, 2⟩, ⟨(.inl .r3c, true), [1, 2], false, 3⟩, ⟨(.inl .r3c, false), [1, 2], true, 4⟩,
      ⟨(.inl .r2d, false), [1, 2], false, 3⟩, ⟨(.inr .ksym2, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inr .k31, false), [0, 1, 2, 3], true, 3⟩, ⟨(.inl .r1a, false), [1, 2], true, 5⟩,
      ⟨(.inl .r1a, false), [0, 2], false, 4⟩, ⟨(.inl .r3a, false), [0, 2, 3], true, 5⟩, ⟨(.inl .r4a, false), [0, 2, 4, 5], true, 6⟩, ⟨(.inl .r3e, false), [0, 2, 3, 4, 5], true, 5⟩,
      ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r3a, false), [2, 3, 5], true, 6⟩, ⟨(.inl .r3b, false), [2, 3, 5], true, 6⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 2⟩,
      ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 3⟩]
  | true, false, true, true =>
    [⟨(.inl .r1b, false), [2], false, 3⟩, ⟨(.inl .r1b, false), [0], false, 3⟩, ⟨(.inl .r2d, false), [0, 2], true, 4⟩, ⟨(.inl .r2d, false), [0, 2], true, 3⟩,
      ⟨(.inl .r1c, false), [0, 2, 4, 5], false, 5⟩, ⟨(.inl .r1b, false), [1], false, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩, ⟨(.inl .r3c, false), [0, 1], true, 1⟩,
      ⟨(.inl .r1a, false), [1, 2], false, 1⟩, ⟨(.inl .r2b, false), [1, 2, 0], true, 2⟩, ⟨(.inl .r2e, false), [1, 2, 3, 4, 5], true, 5⟩, ⟨(.inl .r2c, false), [0, 1, 2, 3, 4, 5], true, 4⟩,
      ⟨(.inl .r3d, true), [1, 2, 3, 4, 5], false, 3⟩, ⟨(.inl .r3b, false), [0, 1, 2], true, 4⟩, ⟨(.inl .r3b, false), [0, 1, 2], false, 4⟩, ⟨(.inl .r3c, false), [0, 1], true, 5⟩,
      ⟨(.inl .r2b, false), [0, 1, 2], true, 6⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .k22, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inr .ksym2, false), [0, 1, 2, 3], true, 4⟩,
      ⟨(.inl .r3b, false), [0, 1, 2], true, 5⟩, ⟨(.inl .r3b, true), [1, 2, 3], true, 6⟩, ⟨(.inl .r2b, false), [1, 3, 0], true, 7⟩, ⟨(.inl .r3c, true), [1, 3], false, 8⟩,
      ⟨(.inl .r2b, false), [1, 3, 2], true, 9⟩, ⟨(.inl .r2d, false), [2, 3], false, 8⟩, ⟨(.inl .r3c, false), [1, 3], true, 10⟩, ⟨(.inl .r1a, false), [1, 3], true, 11⟩,
      ⟨(.inl .r2d, false), [1, 3], false, 9⟩, ⟨(.inl .r2d, false), [1, 2], false, 8⟩, ⟨(.inl .r2d, false), [1, 2], true, 8⟩, ⟨(.inl .r2d, false), [1, 3], true, 9⟩,
      ⟨(.inl .r1b, false), [1], true, 10⟩, ⟨(.inl .r1b, false), [3], true, 9⟩, ⟨(.inl .r1b, false), [2], true, 8⟩, ⟨(.inl .r1b, false), [0], true, 7⟩,
      ⟨(.inl .r3e, false), [0, 2, 3, 4, 5], true, 6⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 5⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 4⟩]
  | true, true, false, true =>
    [⟨(.inl .r1b, false), [2], false, 4⟩, ⟨(.inl .r1c, false), [0, 2, 4, 5], false, 5⟩, ⟨(.inl .r1b, false), [1], false, 0⟩, ⟨(.inl .r1a, false), [1, 2], false, 0⟩,
      ⟨(.inl .r3c, true), [1, 2], false, 1⟩, ⟨(.inl .r1a, false), [1, 3], false, 2⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 1⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 0⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], true, 0⟩, ⟨(.inl .r1a, false), [4, 5], false, 2⟩, ⟨(.inl .r2b, false), [4, 5, 2], true, 3⟩, ⟨(.inl .r2e, false), [1, 2, 3, 4, 5], true, 7⟩,
      ⟨(.inl .r3d, true), [1, 2, 3, 4, 5], false, 6⟩, ⟨(.inl .r4a, false), [1, 3, 4, 5], true, 5⟩, ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 4⟩, ⟨(.inl .r1a, false), [3, 5], true, 5⟩,
      ⟨(.inl .r2b, false), [1, 2, 5], false, 6⟩, ⟨(.inl .r2b, false), [1, 2, 3], false, 5⟩, ⟨(.inl .r2d, false), [1, 5], false, 7⟩, ⟨(.inl .r2d, false), [1, 3], false, 6⟩,
      ⟨(.inl .r2d, false), [2, 5], false, 8⟩, ⟨(.inl .r2d, false), [2, 3], false, 7⟩, ⟨(.inl .r2d, false), [3, 5], false, 9⟩, ⟨(.inl .r1b, false), [3], true, 8⟩,
      ⟨(.inl .r3c, true), [1, 2], false, 5⟩, ⟨(.inl .r3c, false), [1, 2], true, 6⟩, ⟨(.inl .r2d, false), [1, 2], false, 5⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 8⟩,
      ⟨(.inr .ksym2, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .k31, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r1a, false), [1, 2], true, 7⟩, ⟨(.inl .r2d, false), [2, 5], false, 7⟩,
      ⟨(.inl .r1a, false), [0, 2], false, 9⟩, ⟨(.inl .r2b, false), [0, 2, 5], false, 8⟩, ⟨(.inl .r3c, true), [0, 2], true, 7⟩, ⟨(.inl .r3a, true), [0, 2, 3], true, 6⟩,
      ⟨(.inl .r4a, false), [0, 2, 4, 5], true, 10⟩, ⟨(.inr .k32, false), [0, 2, 4, 5], true, 8⟩, ⟨(.inl .r3e, false), [0, 2, 3, 4, 5], true, 7⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 6⟩,
      ⟨(.inl .r3b, true), [0, 2, 3], true, 7⟩, ⟨(.inl .r3a, false), [0, 3, 5], true, 8⟩, ⟨(.inl .r3b, false), [0, 3, 5], true, 8⟩, ⟨(.inl .r2a, false), [0, 5, 2, 3], false, 7⟩,
      ⟨(.inl .r3b, true), [2, 3, 5], true, 8⟩, ⟨(.inl .r3a, true), [2, 4, 5], true, 9⟩, ⟨(.inl .r2a, false), [2, 4, 3, 5], false, 8⟩, ⟨(.inl .r3c, true), [2, 5], true, 14⟩,
      ⟨(.inl .r2b, false), [2, 5, 4], false, 13⟩, ⟨(.inl .r3c, false), [2, 5], false, 12⟩, ⟨(.inl .r2b, false), [2, 5, 0], false, 11⟩, ⟨(.inl .r3b, true), [2, 4, 5], false, 10⟩,
      ⟨(.inl .r2a, false), [2, 4, 3, 5], false, 9⟩, ⟨(.inl .r1a, false), [2, 4], true, 8⟩, ⟨(.inl .r2d, false), [4, 5], false, 11⟩, ⟨(.inl .r2d, false), [2, 5], false, 12⟩,
      ⟨(.inl .r2d, false), [2, 4], false, 11⟩, ⟨(.inl .r2d, false), [2, 4], true, 11⟩, ⟨(.inl .r2d, false), [2, 5], true, 12⟩, ⟨(.inl .r1b, false), [2], true, 13⟩,
      ⟨(.inl .r1b, false), [5], true, 12⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 5⟩]
  | true, true, true, false =>
    [⟨(.inl .r1b, false), [0], false, 4⟩, ⟨(.inl .r1c, false), [0, 2, 4, 5], false, 5⟩, ⟨(.inl .r1b, false), [1], false, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩,
      ⟨(.inl .r3c, false), [0, 1], true, 1⟩, ⟨(.inl .r1a, false), [1, 2], false, 1⟩, ⟨(.inl .r2b, false), [1, 2, 0], true, 2⟩, ⟨(.inl .r1a, false), [1, 3], false, 3⟩,
      ⟨(.inl .r2b, false), [1, 3, 0], false, 2⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 1⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 1⟩, ⟨(.inl .r1a, false), [4, 5], false, 3⟩,
      ⟨(.inl .r2b, false), [4, 5, 0], true, 4⟩, ⟨(.inl .r2e, false), [1, 2, 3, 4, 5], true, 9⟩, ⟨(.inl .r2c, false), [0, 1, 2, 3, 4, 5], true, 8⟩, ⟨(.inl .r3d, true), [1, 2, 3, 4, 5], false, 7⟩,
      ⟨(.inl .r4a, false), [1, 3, 4, 5], true, 6⟩, ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 5⟩, ⟨(.inl .r1a, false), [3, 5], true, 6⟩, ⟨(.inl .r2b, false), [1, 2, 5], false, 7⟩,
      ⟨(.inl .r2b, false), [1, 2, 3], false, 6⟩, ⟨(.inl .r2b, false), [0, 1, 5], false, 8⟩, ⟨(.inl .r2b, false), [0, 1, 3], false, 7⟩, ⟨(.inl .r3b, false), [0, 1, 2], true, 6⟩,
      ⟨(.inl .r2d, false), [1, 5], false, 9⟩, ⟨(.inl .r2d, false), [1, 3], false, 8⟩, ⟨(.inl .r2d, false), [2, 5], false, 10⟩, ⟨(.inl .r2d, false), [2, 3], false, 9⟩,
      ⟨(.inl .r2d, false), [3, 5], false, 11⟩, ⟨(.inl .r1b, false), [3], true, 10⟩, ⟨(.inl .r3b, false), [0, 1, 2], false, 6⟩, ⟨(.inl .r3c, false), [0, 1], true, 7⟩,
      ⟨(.inl .r2b, false), [0, 1, 2], true, 8⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 10⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 9⟩, ⟨(.inr .k22, false), [0, 1, 2, 3], true, 7⟩,
      ⟨(.inr .ksym2, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inl .r3b, false), [0, 1, 2], true, 7⟩, ⟨(.inl .r3b, true), [1, 2, 3], true, 8⟩, ⟨(.inl .r2b, false), [1, 3, 0], true, 9⟩,
      ⟨(.inl .r3c, true), [1, 3], false, 10⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 11⟩, ⟨(.inl .r2d, false), [2, 3], false, 10⟩, ⟨(.inl .r3c, false), [1, 3], true, 12⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 13⟩, ⟨(.inl .r2d, false), [1, 3], false, 11⟩, ⟨(.inl .r2d, false), [1, 2], false, 10⟩, ⟨(.inl .r2d, false), [1, 2], true, 10⟩,
      ⟨(.inl .r2d, false), [1, 3], true, 11⟩, ⟨(.inl .r1b, false), [1], true, 12⟩, ⟨(.inl .r1b, false), [3], true, 11⟩, ⟨(.inl .r2d, false), [0, 2], true, 9⟩,
      ⟨(.inl .r2d, false), [0, 5], true, 10⟩, ⟨(.inl .r1b, false), [0], true, 11⟩, ⟨(.inl .r3c, true), [2, 3], false, 8⟩, ⟨(.inl .r2b, false), [2, 3, 5], true, 9⟩,
      ⟨(.inl .r2b, false), [0, 2, 3], true, 7⟩, ⟨(.inl .r2b, false), [0, 2, 5], true, 8⟩, ⟨(.inl .r3e, false), [0, 2, 3, 4, 5], true, 10⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 9⟩,
      ⟨(.inr .k21, false), [2, 3, 4, 5], true, 7⟩, ⟨(.inl .r2a, false), [0, 2, 4, 5], false, 9⟩, ⟨(.inl .r3b, false), [0, 2, 3], true, 8⟩, ⟨(.inl .r2a, false), [2, 3, 4, 5], false, 10⟩,
      ⟨(.inl .r1a, false), [2, 3], true, 9⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 5⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 6⟩]
  | _, _, _, _ => []

theorem chk323_0223 : ∀ x y p q : Bool, xor (xor (xor x y) p) q = true →
    checkD (Gen.k 2 3 4 5 (by decide) (by decide) (by decide) :: (negw x 2 ++ negw y 3) ++ [Gen.k 0 1 2 3 (by decide) (by decide) (by decide)])
      (X323_0223 x y p q ++ Gen.k 0 1 2 4 (by decide) (by decide) (by decide) :: Y323_0223 x y p q ++
        Gen.k 0 2 4 5 (by decide) (by decide) (by decide) :: (negw p 0 ++ negw q 2)) (S323_0223 x y p q) = true := by
  decide +kernel

theorem tag323_0223 : ∀ x y p q : Bool, ∀ g ∈ X323_0223 x y p q ++ Y323_0223 x y p q, g.tag ≠ 2 := by
  decide

/-- Subcase 3.2.3 with `{a,b} = {0,2}`, `{α,β} = {2,3}` (from `0`). -/
theorem rel323_0223 {a0 a1 a2 a3 c d : Fin n} (h1 : a0 < a1) (h2 : a1 < a2) (h3 : a2 < a3) (h4 : a3 < c) (h5 : c < d) (x y p q : Bool)
    (hpar : xor (xor (xor x y) p) q = true) :
    ∃ Xw Yw : List (Gen n), (∀ g ∈ Xw ++ Yw, g.tag ≠ 2 ∧ extent g ≤ d.val) ∧
      Derivable (Table1 n)
        (FreeMonoid.ofList (Gen.k a2 a3 c d h3 h4 h5 :: (negw x a2 ++ negw y a3) ++
          [Gen.k a0 a1 a2 a3 h1 h2 h3]))
        (FreeMonoid.ofList (Xw ++ Gen.k a0 a1 a2 c h1 h2 (h3.trans h4) :: Yw ++
          Gen.k a0 a2 c d (h1.trans h2) (h3.trans h4) h5 :: (negw p a0 ++ negw q a2))) := by
  refine ⟨(X323_0223 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)),
    (Y323_0223 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)), ?_, ?_⟩
  · intro g hg
    rw [← List.map_append] at hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    refine ⟨by rw [tag_rename]; exact tag323_0223 x y p q g' hg', ?_⟩
    have := extent_rename_le (emb6 h1 h2 h3 h4 h5) g' 5 (extent_le_last g')
    rwa [emb6_5] at this
  · have hh := derivable_rename (emb6 h1 h2 h3 h4 h5) (checkD_sound (chk323_0223 x y p q hpar))
    rw [renW_ofList, renW_ofList] at hh
    convert hh using 2 <;>
      simp only [List.map_append, List.map_cons, List.map_nil, negw_rename, Gen.rename, emb6_0,
        emb6_1, emb6_2, emb6_3, emb6_4, emb6_5, List.cons_append, List.nil_append,
        List.append_assoc]

/-- `X` for `{a,b} = {0,3}`, `{α,β} = {0,3}`. -/
def X323_0303 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, false => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 2]
  | false, false, true, true => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 2]
  | false, true, false, true => [Gen.x 0 1 (by decide), Gen.neg 2]
  | false, true, true, false => [Gen.x 0 1 (by decide), Gen.neg 0]
  | true, false, false, true => [Gen.x 0 1 (by decide), Gen.neg 2]
  | true, false, true, false => [Gen.x 0 1 (by decide), Gen.neg 0]
  | true, true, false, false => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 2]
  | true, true, true, true => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 0]
  | _, _, _, _ => []

/-- `Y` for `{a,b} = {0,3}`, `{α,β} = {0,3}`. -/
def Y323_0303 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, false => [Gen.x 0 3 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 1]
  | false, false, true, true => [Gen.x 0 5 (by decide), Gen.x 2 5 (by decide), Gen.x 3 4 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 3, Gen.neg 4, Gen.neg 5]
  | false, true, false, true => [Gen.x 0 2 (by decide), Gen.neg 1]
  | false, true, true, false => [Gen.x 0 2 (by decide), Gen.x 1 2 (by decide), Gen.x 3 5 (by decide), Gen.neg 2, Gen.neg 3, Gen.neg 5]
  | true, false, false, true => [Gen.x 0 2 (by decide), Gen.x 1 2 (by decide), Gen.x 3 5 (by decide), Gen.neg 1, Gen.neg 3, Gen.neg 5]
  | true, false, true, false => [Gen.x 0 2 (by decide), Gen.neg 2]
  | true, true, false, false => [Gen.x 0 5 (by decide), Gen.x 1 5 (by decide), Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 4]
  | true, true, true, true => [Gen.x 0 3 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 2]
  | _, _, _, _ => []

/-- The chains for `{a,b} = {0,3}`, `{α,β} = {0,3}`. -/
def S323_0303 : Bool → Bool → Bool → Bool → List (GStep ((Fam ⊕ MFam) × Bool) 6)
  | false, false, false, false =>
    [⟨(.inl .r1c, false), [0, 3, 4, 5], false, 2⟩, ⟨(.inl .r1b, false), [2], false, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩, ⟨(.inl .r2b, false), [0, 1, 2], true, 1⟩,
      ⟨(.inl .r1a, false), [1, 3], false, 1⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 2⟩, ⟨(.inl .r1a, false), [4, 5], false, 2⟩, ⟨(.inl .r2b, false), [4, 5, 2], true, 3⟩,
      ⟨(.inl .r2e, false), [2, 0, 3, 4, 5], true, 7⟩, ⟨(.inl .r3d, false), [0, 1, 3, 4, 5], true, 6⟩, ⟨(.inl .r4a, false), [1, 3, 4, 5], true, 5⟩, ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 4⟩,
      ⟨(.inl .r1a, false), [3, 5], true, 5⟩, ⟨(.inl .r2b, false), [0, 1, 5], false, 6⟩, ⟨(.inl .r2b, false), [0, 1, 3], false, 5⟩, ⟨(.inl .r2d, false), [2, 5], false, 7⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 6⟩, ⟨(.inl .r2b, false), [0, 1, 2], true, 5⟩, ⟨(.inl .r2b, false), [0, 1, 3], true, 6⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 8⟩,
      ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .k11, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r1a, false), [1, 3], true, 7⟩, ⟨(.inl .r2d, false), [1, 3], true, 7⟩,
      ⟨(.inl .r2d, false), [1, 5], true, 8⟩, ⟨(.inl .r2b, false), [0, 2, 3], true, 6⟩, ⟨(.inl .r2b, false), [0, 2, 5], true, 7⟩, ⟨(.inl .r2e, false), [1, 0, 3, 4, 5], true, 9⟩,
      ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 8⟩, ⟨(.inr .k21, false), [2, 3, 4, 5], true, 6⟩, ⟨(.inl .r2a, false), [0, 2, 4, 5], false, 8⟩, ⟨(.inl .r3b, false), [0, 2, 3], true, 7⟩,
      ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 5⟩]
  | false, false, true, true =>
    [⟨(.inl .r1b, false), [3], false, 2⟩, ⟨(.inl .r1b, false), [0], false, 2⟩, ⟨(.inl .r2d, false), [0, 3], true, 3⟩, ⟨(.inl .r2d, false), [0, 3], true, 2⟩,
      ⟨(.inl .r1c, false), [0, 3, 4, 5], false, 4⟩, ⟨(.inl .r1b, false), [2], false, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩, ⟨(.inl .r2b, false), [0, 1, 2], true, 1⟩,
      ⟨(.inl .r1a, false), [1, 3], false, 1⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 2⟩, ⟨(.inl .r1a, false), [4, 5], false, 2⟩, ⟨(.inl .r2b, false), [4, 5, 2], true, 3⟩,
      ⟨(.inl .r2e, false), [2, 0, 3, 4, 5], true, 7⟩, ⟨(.inl .r3d, false), [0, 1, 3, 4, 5], true, 6⟩, ⟨(.inl .r4a, false), [1, 3, 4, 5], true, 5⟩, ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 4⟩,
      ⟨(.inl .r1a, false), [3, 5], true, 5⟩, ⟨(.inl .r2b, false), [0, 1, 5], false, 6⟩, ⟨(.inl .r2b, false), [0, 1, 3], false, 5⟩, ⟨(.inl .r2d, false), [2, 5], false, 7⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 6⟩, ⟨(.inl .r2b, false), [0, 1, 2], true, 5⟩, ⟨(.inl .r2b, false), [0, 1, 3], true, 6⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 8⟩,
      ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .k11, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r1a, false), [1, 3], true, 7⟩, ⟨(.inl .r2d, false), [3, 5], false, 9⟩,
      ⟨(.inl .r1b, false), [3], true, 8⟩, ⟨(.inl .r2d, false), [0, 5], false, 8⟩, ⟨(.inl .r2d, false), [0, 1], false, 7⟩, ⟨(.inl .r2d, false), [1, 5], true, 8⟩,
      ⟨(.inl .r3c, true), [0, 2], false, 6⟩, ⟨(.inl .r2b, false), [0, 2, 5], true, 7⟩, ⟨(.inl .r2e, false), [1, 0, 3, 4, 5], true, 9⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 8⟩,
      ⟨(.inr .k32, false), [2, 3, 4, 5], true, 6⟩, ⟨(.inl .r2b, false), [0, 2, 5], false, 12⟩, ⟨(.inl .r2b, false), [0, 2, 4], false, 11⟩, ⟨(.inl .r2b, false), [0, 2, 3], false, 10⟩,
      ⟨(.inl .r3c, true), [0, 2], true, 9⟩, ⟨(.inl .r2a, false), [0, 2, 3, 4], false, 8⟩, ⟨(.inl .r3b, false), [0, 2, 5], true, 7⟩, ⟨(.inl .r2d, false), [1, 5], false, 13⟩,
      ⟨(.inl .r2d, false), [1, 4], false, 12⟩, ⟨(.inl .r2d, false), [1, 3], false, 11⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 5⟩]
  | false, true, false, true =>
    [⟨(.inl .r1b, false), [3], false, 3⟩, ⟨(.inl .r1c, false), [0, 3, 4, 5], false, 4⟩, ⟨(.inl .r1b, false), [2], false, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩,
      ⟨(.inl .r2b, false), [0, 1, 2], true, 1⟩, ⟨(.inl .r2e, false), [2, 0, 3, 4, 5], true, 3⟩, ⟨(.inl .r3d, false), [0, 1, 3, 4, 5], true, 2⟩, ⟨(.inl .r2b, false), [0, 1, 2], true, 3⟩,
      ⟨(.inl .r2b, false), [0, 1, 3], true, 4⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inr .k11, false), [0, 1, 2, 3], true, 3⟩, ⟨(.inl .r1a, false), [1, 3], true, 5⟩,
      ⟨(.inl .r1b, false), [3], true, 6⟩, ⟨(.inl .r2e, false), [1, 0, 3, 4, 5], true, 5⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 2⟩,
      ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 3⟩]
  | false, true, true, false =>
    [⟨(.inl .r1b, false), [0], false, 3⟩, ⟨(.inl .r1c, false), [0, 3, 4, 5], false, 4⟩, ⟨(.inl .r1b, false), [1], false, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩,
      ⟨(.inl .r3c, false), [0, 1], true, 1⟩, ⟨(.inl .r2e, false), [1, 0, 3, 4, 5], true, 3⟩, ⟨(.inl .r3d, false), [0, 1, 3, 4, 5], true, 2⟩, ⟨(.inl .r3c, false), [0, 1], true, 3⟩,
      ⟨(.inl .r2b, false), [0, 1, 3], true, 4⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inr .k32, false), [0, 1, 2, 3], true, 3⟩, ⟨(.inl .r2d, false), [1, 2], true, 7⟩,
      ⟨(.inl .r2d, false), [1, 3], true, 8⟩, ⟨(.inl .r2d, false), [2, 3], true, 7⟩, ⟨(.inl .r3c, false), [1, 3], false, 9⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 8⟩,
      ⟨(.inl .r3c, true), [1, 3], true, 7⟩, ⟨(.inl .r2b, false), [1, 3, 0], false, 6⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 5⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 5⟩,
      ⟨(.inl .r2d, false), [1, 2], true, 8⟩, ⟨(.inl .r2d, false), [1, 3], true, 9⟩, ⟨(.inl .r1b, false), [1], true, 10⟩, ⟨(.inl .r1b, false), [3], true, 9⟩,
      ⟨(.inl .r2d, false), [0, 2], false, 8⟩, ⟨(.inl .r1b, false), [0], true, 7⟩, ⟨(.inl .r3b, false), [0, 1, 3], false, 4⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 5⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], false, 4⟩, ⟨(.inl .r2e, false), [2, 0, 3, 4, 5], true, 7⟩, ⟨(.inl .r3d, false), [0, 1, 3, 4, 5], true, 6⟩, ⟨(.inl .r3d, false), [1, 2, 3, 4, 5], true, 5⟩,
      ⟨(.inl .r4a, false), [2, 3, 4, 5], true, 4⟩, ⟨(.inl .r2b, false), [1, 2, 5], false, 7⟩, ⟨(.inl .r2b, false), [1, 2, 3], false, 6⟩, ⟨(.inl .r2a, false), [1, 2, 3, 5], false, 5⟩,
      ⟨(.inl .r2b, false), [0, 1, 5], false, 8⟩, ⟨(.inl .r2b, false), [0, 1, 3], false, 7⟩, ⟨(.inl .r2a, false), [0, 1, 3, 5], false, 6⟩, ⟨(.inl .r3b, false), [0, 1, 2], true, 5⟩,
      ⟨(.inl .r2d, false), [2, 5], false, 9⟩, ⟨(.inl .r2d, false), [2, 3], false, 8⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 2⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 3⟩]
  | true, false, false, true =>
    [⟨(.inl .r1b, false), [3], false, 3⟩, ⟨(.inl .r1c, false), [0, 3, 4, 5], false, 4⟩, ⟨(.inl .r1b, false), [2], false, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩,
      ⟨(.inl .r2b, false), [0, 1, 2], true, 1⟩, ⟨(.inl .r2e, false), [2, 0, 3, 4, 5], true, 3⟩, ⟨(.inl .r3d, false), [0, 1, 3, 4, 5], true, 2⟩, ⟨(.inl .r2d, false), [0, 2], false, 4⟩,
      ⟨(.inl .r3c, true), [0, 1], false, 3⟩, ⟨(.inl .r2b, false), [0, 1, 2], true, 4⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inr .k31, false), [0, 1, 2, 3], true, 3⟩,
      ⟨(.inl .r3a, false), [1, 2, 3], true, 5⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 5⟩, ⟨(.inl .r1b, false), [3], true, 8⟩, ⟨(.inl .r3b, false), [0, 1, 3], false, 4⟩,
      ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r3b, false), [1, 2, 3], false, 4⟩, ⟨(.inl .r2e, false), [1, 0, 3, 4, 5], true, 7⟩, ⟨(.inl .r3d, false), [0, 1, 3, 4, 5], true, 6⟩,
      ⟨(.inl .r3d, false), [1, 2, 3, 4, 5], true, 5⟩, ⟨(.inl .r4a, false), [2, 3, 4, 5], true, 4⟩, ⟨(.inl .r2b, false), [1, 2, 5], false, 7⟩, ⟨(.inl .r2b, false), [1, 2, 3], false, 6⟩,
      ⟨(.inl .r2a, false), [1, 2, 3, 5], false, 5⟩, ⟨(.inl .r2b, false), [0, 1, 5], false, 8⟩, ⟨(.inl .r2b, false), [0, 1, 3], false, 7⟩, ⟨(.inl .r2a, false), [0, 1, 3, 5], false, 6⟩,
      ⟨(.inl .r3b, false), [0, 1, 2], true, 5⟩, ⟨(.inl .r2d, false), [1, 5], false, 9⟩, ⟨(.inl .r2d, false), [1, 3], false, 8⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 2⟩,
      ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 3⟩]
  | true, false, true, false =>
    [⟨(.inl .r1b, false), [0], false, 3⟩, ⟨(.inl .r1c, false), [0, 3, 4, 5], false, 4⟩, ⟨(.inl .r1b, false), [1], false, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩,
      ⟨(.inl .r3c, false), [0, 1], true, 1⟩, ⟨(.inl .r2e, false), [1, 0, 3, 4, 5], true, 3⟩, ⟨(.inl .r3d, false), [0, 1, 3, 4, 5], true, 2⟩, ⟨(.inl .r2d, false), [0, 1], false, 4⟩,
      ⟨(.inl .r3c, true), [0, 1], false, 3⟩, ⟨(.inl .r3c, false), [0, 1], true, 4⟩, ⟨(.inl .r2d, false), [0, 1], false, 3⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 5⟩,
      ⟨(.inr .k12, false), [0, 1, 2, 3], true, 3⟩, ⟨(.inl .r2b, false), [1, 3, 0], true, 5⟩, ⟨(.inl .r3c, true), [1, 3], false, 6⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 7⟩,
      ⟨(.inl .r3c, false), [1, 3], true, 8⟩, ⟨(.inl .r1a, false), [1, 3], true, 9⟩, ⟨(.inl .r2d, false), [2, 3], false, 6⟩, ⟨(.inl .r2d, false), [1, 3], false, 7⟩,
      ⟨(.inl .r2d, false), [1, 2], false, 6⟩, ⟨(.inl .r2d, false), [1, 2], true, 6⟩, ⟨(.inl .r2d, false), [1, 3], true, 7⟩, ⟨(.inl .r1b, false), [1], true, 8⟩,
      ⟨(.inl .r1b, false), [3], true, 7⟩, ⟨(.inl .r2d, false), [0, 2], false, 6⟩, ⟨(.inl .r1b, false), [0], true, 5⟩, ⟨(.inl .r2e, false), [2, 0, 3, 4, 5], true, 5⟩,
      ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 2⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 3⟩]
  | true, true, false, false =>
    [⟨(.inl .r1c, false), [0, 3, 4, 5], false, 4⟩, ⟨(.inl .r1b, false), [2], false, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩, ⟨(.inl .r2b, false), [0, 1, 2], true, 1⟩,
      ⟨(.inl .r1a, false), [1, 3], false, 1⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 2⟩, ⟨(.inl .r1a, false), [4, 5], false, 2⟩, ⟨(.inl .r2b, false), [4, 5, 2], true, 3⟩,
      ⟨(.inl .r2e, false), [2, 0, 3, 4, 5], true, 7⟩, ⟨(.inl .r3d, false), [0, 1, 3, 4, 5], true, 6⟩, ⟨(.inl .r4a, false), [1, 3, 4, 5], true, 5⟩, ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 4⟩,
      ⟨(.inl .r1a, false), [3, 5], true, 5⟩, ⟨(.inl .r2b, false), [0, 1, 5], false, 6⟩, ⟨(.inl .r2b, false), [0, 1, 3], false, 5⟩, ⟨(.inl .r2d, false), [2, 5], false, 7⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 6⟩, ⟨(.inl .r2d, false), [0, 5], false, 8⟩, ⟨(.inl .r2d, false), [0, 3], false, 7⟩, ⟨(.inl .r2d, false), [0, 2], false, 6⟩,
      ⟨(.inl .r2d, false), [3, 5], false, 9⟩, ⟨(.inl .r1b, false), [3], true, 8⟩, ⟨(.inl .r3c, true), [0, 1], false, 5⟩, ⟨(.inl .r2b, false), [0, 1, 2], true, 6⟩,
      ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 8⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .k31, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 7⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], true, 7⟩, ⟨(.inl .r2d, false), [1, 3], true, 9⟩, ⟨(.inl .r2d, false), [1, 5], true, 10⟩, ⟨(.inl .r3b, false), [0, 1, 3], false, 6⟩,
      ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inl .r2b, false), [0, 1, 3], true, 8⟩, ⟨(.inl .r2b, false), [0, 1, 5], true, 9⟩, ⟨(.inl .r3b, false), [1, 2, 3], false, 6⟩,
      ⟨(.inl .r2b, false), [1, 2, 3], true, 7⟩, ⟨(.inl .r2b, false), [1, 2, 5], true, 8⟩, ⟨(.inl .r3c, false), [2, 3], true, 6⟩, ⟨(.inl .r2b, false), [2, 3, 5], true, 7⟩,
      ⟨(.inl .r2e, false), [1, 0, 3, 4, 5], true, 11⟩, ⟨(.inl .r3d, false), [0, 1, 3, 4, 5], true, 10⟩, ⟨(.inl .r3d, false), [1, 2, 3, 4, 5], true, 9⟩, ⟨(.inl .r4a, false), [2, 3, 4, 5], true, 8⟩,
      ⟨(.inr .k32, false), [2, 3, 4, 5], true, 6⟩, ⟨(.inl .r2d, false), [3, 4], true, 10⟩, ⟨(.inl .r2d, false), [3, 5], true, 11⟩, ⟨(.inl .r2d, false), [4, 5], true, 10⟩,
      ⟨(.inl .r3c, false), [3, 5], false, 12⟩, ⟨(.inl .r2b, false), [3, 5, 4], false, 11⟩, ⟨(.inl .r3c, true), [3, 5], true, 10⟩, ⟨(.inl .r2b, false), [3, 5, 2], false, 9⟩,
      ⟨(.inl .r3a, false), [3, 4, 5], true, 8⟩, ⟨(.inl .r3b, false), [3, 4, 5], true, 8⟩, ⟨(.inl .r2d, false), [3, 4], true, 11⟩, ⟨(.inl .r2d, false), [3, 5], true, 12⟩,
      ⟨(.inl .r1b, false), [3], true, 13⟩, ⟨(.inl .r1b, false), [5], true, 12⟩, ⟨(.inl .r2b, false), [1, 2, 4], false, 11⟩, ⟨(.inl .r3c, true), [1, 2], true, 10⟩,
      ⟨(.inl .r2a, false), [1, 2, 4, 5], false, 9⟩, ⟨(.inl .r2a, false), [1, 2, 3, 5], false, 8⟩, ⟨(.inl .r3b, false), [1, 2, 5], true, 7⟩, ⟨(.inl .r2b, false), [0, 1, 4], false, 12⟩,
      ⟨(.inl .r3c, true), [0, 1], true, 11⟩, ⟨(.inl .r2a, false), [0, 1, 4, 5], false, 10⟩, ⟨(.inl .r2a, false), [0, 1, 3, 5], false, 9⟩, ⟨(.inl .r2a, false), [0, 1, 2, 5], false, 8⟩,
      ⟨(.inl .r3b, false), [0, 1, 5], true, 7⟩, ⟨(.inl .r2d, false), [1, 4], false, 13⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 5⟩]
  | true, true, true, true =>
    [⟨(.inl .r1b, false), [3], false, 4⟩, ⟨(.inl .r1b, false), [0], false, 4⟩, ⟨(.inl .r2d, false), [0, 3], true, 5⟩, ⟨(.inl .r2d, false), [0, 3], true, 4⟩,
      ⟨(.inl .r1c, false), [0, 3, 4, 5], false, 6⟩, ⟨(.inl .r1b, false), [1], false, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩, ⟨(.inl .r3c, false), [0, 1], true, 1⟩,
      ⟨(.inl .r1a, false), [1, 3], false, 1⟩, ⟨(.inl .r2b, false), [1, 3, 0], true, 2⟩, ⟨(.inl .r1a, false), [4, 5], false, 2⟩, ⟨(.inl .r2b, false), [4, 5, 0], true, 3⟩,
      ⟨(.inl .r2e, false), [1, 0, 3, 4, 5], true, 7⟩, ⟨(.inl .r3d, false), [0, 1, 3, 4, 5], true, 6⟩, ⟨(.inl .r4a, false), [1, 3, 4, 5], true, 5⟩, ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 4⟩,
      ⟨(.inl .r1a, false), [3, 5], true, 5⟩, ⟨(.inl .r2b, false), [0, 1, 5], false, 6⟩, ⟨(.inl .r2b, false), [0, 1, 3], false, 5⟩, ⟨(.inl .r2d, false), [1, 5], false, 7⟩,
      ⟨(.inl .r2d, false), [1, 3], false, 6⟩, ⟨(.inl .r2d, false), [0, 5], false, 8⟩, ⟨(.inl .r2d, false), [0, 3], false, 7⟩, ⟨(.inl .r2d, false), [0, 1], false, 6⟩,
      ⟨(.inl .r2d, false), [3, 5], false, 9⟩, ⟨(.inl .r1b, false), [3], true, 8⟩, ⟨(.inl .r3c, true), [0, 1], false, 5⟩, ⟨(.inl .r3c, false), [0, 1], true, 6⟩,
      ⟨(.inl .r2d, false), [0, 1], false, 5⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 8⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 5⟩,
      ⟨(.inl .r2b, false), [1, 3, 0], true, 7⟩, ⟨(.inl .r3c, true), [1, 3], false, 8⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 9⟩, ⟨(.inl .r3c, false), [1, 3], true, 10⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 11⟩, ⟨(.inl .r2d, false), [2, 3], false, 8⟩, ⟨(.inl .r2d, false), [1, 3], false, 9⟩, ⟨(.inl .r2d, false), [1, 2], false, 8⟩,
      ⟨(.inl .r2d, false), [1, 2], true, 8⟩, ⟨(.inl .r2d, false), [1, 3], true, 9⟩, ⟨(.inl .r1b, false), [1], true, 10⟩, ⟨(.inl .r1b, false), [3], true, 9⟩,
      ⟨(.inl .r2d, false), [3, 5], false, 9⟩, ⟨(.inl .r2d, false), [0, 2], true, 7⟩, ⟨(.inl .r2d, false), [0, 3], true, 8⟩, ⟨(.inl .r2d, false), [0, 5], true, 9⟩,
      ⟨(.inl .r1b, false), [0], true, 10⟩, ⟨(.inl .r2d, false), [2, 3], true, 7⟩, ⟨(.inl .r2d, false), [2, 5], true, 8⟩, ⟨(.inl .r2b, false), [0, 2, 3], true, 6⟩,
      ⟨(.inl .r2b, false), [0, 2, 5], true, 7⟩, ⟨(.inl .r2e, false), [2, 0, 3, 4, 5], true, 9⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 8⟩, ⟨(.inr .k21, false), [2, 3, 4, 5], true, 6⟩,
      ⟨(.inl .r2a, false), [0, 2, 4, 5], false, 8⟩, ⟨(.inl .r3b, false), [0, 2, 3], true, 7⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 5⟩]
  | _, _, _, _ => []

theorem chk323_0303 : ∀ x y p q : Bool, xor (xor (xor x y) p) q = false →
    checkD (Gen.k 0 3 4 5 (by decide) (by decide) (by decide) :: (negw x 0 ++ negw y 3) ++ [Gen.k 0 1 2 3 (by decide) (by decide) (by decide)])
      (X323_0303 x y p q ++ Gen.k 0 1 2 4 (by decide) (by decide) (by decide) :: Y323_0303 x y p q ++
        Gen.k 0 3 4 5 (by decide) (by decide) (by decide) :: (negw p 0 ++ negw q 3)) (S323_0303 x y p q) = true := by
  decide +kernel

theorem tag323_0303 : ∀ x y p q : Bool, ∀ g ∈ X323_0303 x y p q ++ Y323_0303 x y p q, g.tag ≠ 2 := by
  decide

/-- Subcase 3.2.3 with `{a,b} = {0,3}`, `{α,β} = {0,3}` (from `0`). -/
theorem rel323_0303 {a0 a1 a2 a3 c d : Fin n} (h1 : a0 < a1) (h2 : a1 < a2) (h3 : a2 < a3) (h4 : a3 < c) (h5 : c < d) (x y p q : Bool)
    (hpar : xor (xor (xor x y) p) q = false) :
    ∃ Xw Yw : List (Gen n), (∀ g ∈ Xw ++ Yw, g.tag ≠ 2 ∧ extent g ≤ d.val) ∧
      Derivable (Table1 n)
        (FreeMonoid.ofList (Gen.k a0 a3 c d (h1.trans (h2.trans h3)) h4 h5 :: (negw x a0 ++ negw y a3) ++
          [Gen.k a0 a1 a2 a3 h1 h2 h3]))
        (FreeMonoid.ofList (Xw ++ Gen.k a0 a1 a2 c h1 h2 (h3.trans h4) :: Yw ++
          Gen.k a0 a3 c d (h1.trans (h2.trans h3)) h4 h5 :: (negw p a0 ++ negw q a3))) := by
  refine ⟨(X323_0303 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)),
    (Y323_0303 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)), ?_, ?_⟩
  · intro g hg
    rw [← List.map_append] at hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    refine ⟨by rw [tag_rename]; exact tag323_0303 x y p q g' hg', ?_⟩
    have := extent_rename_le (emb6 h1 h2 h3 h4 h5) g' 5 (extent_le_last g')
    rwa [emb6_5] at this
  · have hh := derivable_rename (emb6 h1 h2 h3 h4 h5) (checkD_sound (chk323_0303 x y p q hpar))
    rw [renW_ofList, renW_ofList] at hh
    convert hh using 2 <;>
      simp only [List.map_append, List.map_cons, List.map_nil, negw_rename, Gen.rename, emb6_0,
        emb6_1, emb6_2, emb6_3, emb6_4, emb6_5, List.cons_append, List.nil_append,
        List.append_assoc]

/-- `X` for `{a,b} = {0,3}`, `{α,β} = {1,2}`. -/
def X323_0312 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, true => [Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 2]
  | false, false, true, false => [Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 2]
  | false, true, false, false => [Gen.x 2 3 (by decide), Gen.neg 2]
  | false, true, true, true => [Gen.x 0 3 (by decide), Gen.x 2 3 (by decide), Gen.neg 0]
  | true, false, false, false => [Gen.x 2 3 (by decide), Gen.neg 2]
  | true, false, true, true => [Gen.x 2 3 (by decide), Gen.neg 0]
  | true, true, false, true => [Gen.x 1 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 1]
  | true, true, true, false => [Gen.x 0 3 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 0]
  | _, _, _, _ => []

/-- `Y` for `{a,b} = {0,3}`, `{α,β} = {1,2}`. -/
def Y323_0312 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, true => [Gen.x 0 3 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide)]
  | false, false, true, false => [Gen.x 0 5 (by decide), Gen.x 2 5 (by decide), Gen.x 3 4 (by decide), Gen.neg 0, Gen.neg 3, Gen.neg 4, Gen.neg 5]
  | false, true, false, false => [Gen.x 0 2 (by decide)]
  | false, true, true, true => [Gen.x 0 2 (by decide), Gen.x 3 5 (by decide), Gen.neg 3, Gen.neg 5]
  | true, false, false, false => [Gen.x 0 2 (by decide), Gen.x 1 2 (by decide), Gen.x 3 5 (by decide), Gen.neg 3, Gen.neg 5]
  | true, false, true, true => [Gen.x 0 2 (by decide), Gen.neg 1, Gen.neg 2]
  | true, true, false, true => [Gen.x 0 5 (by decide), Gen.x 1 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 0, Gen.neg 4]
  | true, true, true, false => [Gen.x 0 3 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide)]
  | _, _, _, _ => []

/-- The chains for `{a,b} = {0,3}`, `{α,β} = {1,2}`. -/
def S323_0312 : Bool → Bool → Bool → Bool → List (GStep ((Fam ⊕ MFam) × Bool) 6)
  | false, false, false, true =>
    [⟨(.inl .r1b, false), [3], false, 2⟩, ⟨(.inl .r1c, false), [0, 3, 4, 5], false, 3⟩, ⟨(.inl .r1b, false), [3], false, 0⟩, ⟨(.inl .r1a, false), [1, 2], false, 0⟩,
      ⟨(.inl .r2b, false), [1, 2, 3], true, 1⟩, ⟨(.inl .r1a, false), [2, 3], false, 1⟩, ⟨(.inl .r3c, false), [2, 3], true, 2⟩, ⟨(.inl .r1a, false), [4, 5], false, 2⟩,
      ⟨(.inl .r2b, false), [4, 5, 2], true, 3⟩, ⟨(.inl .r2e, false), [3, 1, 2, 4, 5], true, 7⟩, ⟨(.inl .r4a, false), [1, 2, 4, 5], true, 6⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 5⟩,
      ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 4⟩, ⟨(.inl .r3b, false), [2, 3, 5], true, 5⟩, ⟨(.inl .r3b, false), [2, 3, 5], false, 5⟩, ⟨(.inl .r3a, false), [2, 3, 5], false, 5⟩,
      ⟨(.inl .r1a, false), [2, 5], true, 6⟩, ⟨(.inl .r2d, false), [3, 5], false, 7⟩, ⟨(.inl .r3c, true), [2, 3], false, 5⟩, ⟨(.inl .r3c, false), [2, 3], true, 6⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 5⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 8⟩, ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .k11, false), [0, 1, 2, 3], true, 5⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 7⟩, ⟨(.inl .r2d, false), [3, 5], false, 7⟩, ⟨(.inl .r2b, false), [0, 2, 3], true, 6⟩, ⟨(.inl .r2b, false), [0, 2, 5], true, 7⟩,
      ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 8⟩, ⟨(.inr .k21, false), [2, 3, 4, 5], true, 6⟩, ⟨(.inl .r2a, false), [0, 2, 4, 5], false, 8⟩, ⟨(.inl .r3b, false), [0, 2, 3], true, 7⟩,
      ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 5⟩]
  | false, false, true, false =>
    [⟨(.inl .r1b, false), [0], false, 2⟩, ⟨(.inl .r1c, false), [0, 3, 4, 5], false, 3⟩, ⟨(.inl .r1b, false), [3], false, 0⟩, ⟨(.inl .r1a, false), [1, 2], false, 0⟩,
      ⟨(.inl .r2b, false), [1, 2, 3], true, 1⟩, ⟨(.inl .r1a, false), [2, 3], false, 1⟩, ⟨(.inl .r3c, false), [2, 3], true, 2⟩, ⟨(.inl .r1a, false), [4, 5], false, 2⟩,
      ⟨(.inl .r2b, false), [4, 5, 2], true, 3⟩, ⟨(.inl .r2e, false), [3, 1, 2, 4, 5], true, 7⟩, ⟨(.inl .r4a, false), [1, 2, 4, 5], true, 6⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 5⟩,
      ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 4⟩, ⟨(.inl .r3b, false), [2, 3, 5], true, 5⟩, ⟨(.inl .r3b, false), [2, 3, 5], false, 5⟩, ⟨(.inl .r3a, false), [2, 3, 5], false, 5⟩,
      ⟨(.inl .r1a, false), [2, 5], true, 6⟩, ⟨(.inl .r2d, false), [3, 5], false, 7⟩, ⟨(.inl .r3c, true), [2, 3], false, 5⟩, ⟨(.inl .r3c, false), [2, 3], true, 6⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 5⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 8⟩, ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .k11, false), [0, 1, 2, 3], true, 5⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 7⟩, ⟨(.inl .r2d, false), [0, 5], false, 7⟩, ⟨(.inl .r3c, true), [0, 2], false, 6⟩, ⟨(.inl .r2b, false), [0, 2, 5], true, 7⟩,
      ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 8⟩, ⟨(.inr .k32, false), [2, 3, 4, 5], true, 6⟩, ⟨(.inl .r2b, false), [0, 2, 5], false, 12⟩, ⟨(.inl .r2b, false), [0, 2, 4], false, 11⟩,
      ⟨(.inl .r2b, false), [0, 2, 3], false, 10⟩, ⟨(.inl .r3c, true), [0, 2], true, 9⟩, ⟨(.inl .r2a, false), [0, 2, 3, 4], false, 8⟩, ⟨(.inl .r3b, false), [0, 2, 5], true, 7⟩,
      ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 5⟩]
  | false, true, false, false =>
    [⟨(.inl .r1c, false), [0, 3, 4, 5], false, 3⟩, ⟨(.inl .r1b, false), [3], false, 0⟩, ⟨(.inl .r1a, false), [2, 3], false, 0⟩, ⟨(.inl .r3c, false), [2, 3], true, 1⟩,
      ⟨(.inl .r2e, false), [3, 1, 2, 4, 5], true, 3⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 2⟩, ⟨(.inl .r2d, false), [2, 3], false, 4⟩, ⟨(.inl .r3c, true), [2, 3], false, 3⟩,
      ⟨(.inl .r3c, false), [2, 3], true, 4⟩, ⟨(.inl .r2d, false), [2, 3], false, 3⟩, ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inr .k11, false), [0, 1, 2, 3], true, 3⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 5⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 2⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 3⟩]
  | false, true, true, true =>
    [⟨(.inl .r1b, false), [3], false, 3⟩, ⟨(.inl .r1b, false), [0], false, 3⟩, ⟨(.inl .r2d, false), [0, 3], true, 4⟩, ⟨(.inl .r2d, false), [0, 3], true, 3⟩,
      ⟨(.inl .r1c, false), [0, 3, 4, 5], false, 5⟩, ⟨(.inl .r1b, false), [3], false, 0⟩, ⟨(.inl .r1a, false), [0, 3], false, 0⟩, ⟨(.inl .r3c, false), [0, 3], true, 1⟩,
      ⟨(.inl .r1a, false), [2, 3], false, 1⟩, ⟨(.inl .r2b, false), [2, 3, 0], true, 2⟩, ⟨(.inl .r2e, false), [3, 1, 2, 4, 5], true, 5⟩, ⟨(.inl .r2c, false), [0, 3, 1, 2, 4, 5], true, 4⟩,
      ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r3b, true), [0, 2, 3], false, 4⟩, ⟨(.inl .r2d, false), [2, 3], false, 6⟩, ⟨(.inl .r3a, true), [0, 2, 3], false, 4⟩,
      ⟨(.inl .r3c, false), [0, 2], true, 5⟩, ⟨(.inl .r2b, false), [0, 2, 3], true, 6⟩, ⟨(.inl .r3c, true), [0, 3], false, 4⟩, ⟨(.inl .r3c, false), [0, 3], true, 5⟩,
      ⟨(.inl .r2d, false), [0, 3], false, 4⟩, ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inr .k32, false), [0, 1, 2, 3], true, 4⟩,
      ⟨(.inl .r2d, false), [1, 2], true, 8⟩, ⟨(.inl .r2d, false), [1, 3], true, 9⟩, ⟨(.inl .r2d, false), [2, 3], true, 8⟩, ⟨(.inl .r3c, false), [1, 3], false, 10⟩,
      ⟨(.inl .r2b, false), [1, 3, 2], false, 9⟩, ⟨(.inl .r3c, true), [1, 3], true, 8⟩, ⟨(.inl .r2b, false), [1, 3, 0], false, 7⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 6⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], true, 6⟩, ⟨(.inl .r2b, false), [2, 3, 0], true, 7⟩, ⟨(.inl .r2b, false), [2, 3, 1], true, 8⟩, ⟨(.inl .r3c, true), [2, 3], false, 9⟩,
      ⟨(.inl .r3c, false), [2, 3], true, 10⟩, ⟨(.inl .r1a, false), [2, 3], true, 11⟩, ⟨(.inl .r2d, false), [2, 3], false, 9⟩, ⟨(.inl .r2b, false), [1, 3, 0], true, 6⟩,
      ⟨(.inl .r3c, true), [1, 3], false, 7⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 8⟩, ⟨(.inl .r3c, false), [1, 3], true, 9⟩, ⟨(.inl .r1a, false), [1, 3], true, 10⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 7⟩, ⟨(.inl .r2d, false), [1, 3], false, 8⟩, ⟨(.inl .r2d, false), [1, 2], false, 7⟩, ⟨(.inl .r2d, false), [1, 2], true, 7⟩,
      ⟨(.inl .r2d, false), [1, 3], true, 8⟩, ⟨(.inl .r1b, false), [1], true, 9⟩, ⟨(.inl .r2d, false), [2, 3], false, 8⟩, ⟨(.inl .r1b, false), [2], true, 7⟩,
      ⟨(.inl .r3c, true), [2, 3], true, 7⟩, ⟨(.inl .r2b, false), [2, 3, 0], false, 6⟩, ⟨(.inl .r1b, false), [2], true, 8⟩, ⟨(.inl .r1b, false), [3], true, 8⟩,
      ⟨(.inl .r1b, false), [0], true, 7⟩, ⟨(.inl .r3b, false), [0, 2, 3], false, 5⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 6⟩, ⟨(.inl .r4a, false), [2, 3, 4, 5], true, 5⟩,
      ⟨(.inl .r2b, false), [0, 2, 5], false, 8⟩, ⟨(.inl .r2b, false), [0, 2, 3], false, 7⟩, ⟨(.inl .r2a, false), [0, 2, 3, 5], false, 6⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 3⟩,
      ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 4⟩]
  | true, false, false, false =>
    [⟨(.inl .r1c, false), [0, 3, 4, 5], false, 3⟩, ⟨(.inl .r1b, false), [3], false, 0⟩, ⟨(.inl .r1a, false), [2, 3], false, 0⟩, ⟨(.inl .r3c, false), [2, 3], true, 1⟩,
      ⟨(.inl .r2e, false), [3, 1, 2, 4, 5], true, 3⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 2⟩, ⟨(.inl .r2d, false), [1, 3], false, 4⟩, ⟨(.inr .k21, false), [0, 1, 2, 3], true, 4⟩,
      ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 3⟩, ⟨(.inl .r3b, false), [0, 1, 3], true, 4⟩, ⟨(.inl .r3b, false), [0, 1, 3], false, 4⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 5⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], false, 4⟩, ⟨(.inl .r3d, false), [0, 1, 3, 4, 5], true, 6⟩, ⟨(.inl .r3d, false), [1, 2, 3, 4, 5], true, 5⟩, ⟨(.inl .r4a, false), [2, 3, 4, 5], true, 4⟩,
      ⟨(.inl .r2b, false), [1, 2, 5], false, 7⟩, ⟨(.inl .r2b, false), [1, 2, 3], false, 6⟩, ⟨(.inl .r2a, false), [1, 2, 3, 5], false, 5⟩, ⟨(.inl .r2b, false), [0, 1, 5], false, 8⟩,
      ⟨(.inl .r2b, false), [0, 1, 3], false, 7⟩, ⟨(.inl .r2a, false), [0, 1, 3, 5], false, 6⟩, ⟨(.inl .r3b, false), [0, 1, 2], true, 5⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 2⟩,
      ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 3⟩]
  | true, false, true, true =>
    [⟨(.inl .r1b, false), [3], false, 3⟩, ⟨(.inl .r1b, false), [0], false, 3⟩, ⟨(.inl .r2d, false), [0, 3], true, 4⟩, ⟨(.inl .r2d, false), [0, 3], true, 3⟩,
      ⟨(.inl .r1c, false), [0, 3, 4, 5], false, 5⟩, ⟨(.inl .r1b, false), [0], false, 0⟩, ⟨(.inl .r1a, false), [2, 3], false, 0⟩, ⟨(.inl .r2b, false), [2, 3, 0], true, 1⟩,
      ⟨(.inl .r2e, false), [0, 1, 2, 4, 5], true, 3⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 2⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 3⟩,
      ⟨(.inl .r2a, false), [0, 2, 1, 3], false, 4⟩, ⟨(.inl .r1a, false), [1, 3], true, 5⟩, ⟨(.inl .r1b, false), [3], true, 8⟩, ⟨(.inl .r2d, false), [0, 1], true, 5⟩,
      ⟨(.inl .r2d, false), [0, 2], true, 6⟩, ⟨(.inl .r1b, false), [0], true, 7⟩, ⟨(.inl .r2d, false), [1, 2], true, 5⟩, ⟨(.inl .r2e, false), [1, 0, 3, 4, 5], true, 6⟩,
      ⟨(.inl .r2e, false), [2, 0, 3, 4, 5], true, 5⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r2d, false), [1, 2], false, 6⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 2⟩,
      ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 3⟩]
  | true, true, false, true =>
    [⟨(.inl .r1b, false), [3], false, 4⟩, ⟨(.inl .r1c, false), [0, 3, 4, 5], false, 5⟩, ⟨(.inl .r1b, false), [3], false, 0⟩, ⟨(.inl .r1a, false), [1, 2], false, 0⟩,
      ⟨(.inl .r2b, false), [1, 2, 3], true, 1⟩, ⟨(.inl .r1a, false), [2, 3], false, 1⟩, ⟨(.inl .r3c, false), [2, 3], true, 2⟩, ⟨(.inl .r3a, true), [1, 2, 3], false, 0⟩,
      ⟨(.inl .r3c, false), [1, 2], true, 1⟩, ⟨(.inl .r1a, false), [4, 5], false, 1⟩, ⟨(.inl .r2b, false), [4, 5, 1], true, 2⟩, ⟨(.inl .r2e, false), [3, 1, 2, 4, 5], true, 7⟩,
      ⟨(.inl .r4a, false), [1, 2, 4, 5], true, 6⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 5⟩, ⟨(.inl .r3d, false), [1, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r4c, false), [2, 3, 4, 5], true, 3⟩,
      ⟨(.inl .r2a, false), [1, 2, 3, 5], false, 4⟩, ⟨(.inl .r3b, false), [2, 3, 5], true, 5⟩, ⟨(.inl .r3b, false), [2, 3, 5], false, 5⟩, ⟨(.inl .r3a, false), [2, 3, 5], false, 5⟩,
      ⟨(.inl .r1a, false), [2, 5], true, 6⟩, ⟨(.inl .r2d, false), [3, 5], false, 7⟩, ⟨(.inl .r2d, false), [1, 5], false, 8⟩, ⟨(.inl .r2d, false), [1, 3], false, 7⟩,
      ⟨(.inl .r2d, false), [1, 2], false, 6⟩, ⟨(.inl .r2d, false), [2, 3], true, 7⟩, ⟨(.inl .r2d, false), [2, 5], true, 8⟩, ⟨(.inl .r1b, false), [2], true, 9⟩,
      ⟨(.inl .r3a, true), [1, 2, 3], false, 4⟩, ⟨(.inl .r3c, true), [1, 2], false, 5⟩, ⟨(.inl .r2b, false), [1, 2, 3], true, 6⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 4⟩,
      ⟨(.inl .r3c, false), [1, 3], true, 5⟩, ⟨(.inl .r2d, false), [1, 2], false, 4⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 8⟩, ⟨(.inr .ksym2, false), [0, 1, 2, 3], true, 7⟩,
      ⟨(.inr .ksym6, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inr .k31, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r3a, false), [1, 2, 3], false, 7⟩, ⟨(.inl .r1a, false), [1, 2], true, 6⟩,
      ⟨(.inl .r2d, false), [3, 5], false, 7⟩, ⟨(.inl .r3b, false), [0, 1, 3], false, 5⟩, ⟨(.inl .r2b, false), [0, 1, 3], true, 6⟩, ⟨(.inl .r2b, false), [0, 1, 5], true, 7⟩,
      ⟨(.inl .r3c, false), [1, 3], true, 5⟩, ⟨(.inl .r2b, false), [1, 3, 5], true, 6⟩, ⟨(.inl .r3d, false), [0, 1, 3, 4, 5], true, 8⟩, ⟨(.inl .r4a, false), [1, 3, 4, 5], true, 7⟩,
      ⟨(.inr .k32, false), [1, 3, 4, 5], true, 5⟩, ⟨(.inl .r2d, false), [3, 4], true, 9⟩, ⟨(.inl .r2d, false), [3, 5], true, 10⟩, ⟨(.inl .r2d, false), [4, 5], true, 9⟩,
      ⟨(.inl .r3c, false), [3, 5], false, 11⟩, ⟨(.inl .r2b, false), [3, 5, 4], false, 10⟩, ⟨(.inl .r3c, true), [3, 5], true, 9⟩, ⟨(.inl .r2b, false), [3, 5, 1], false, 8⟩,
      ⟨(.inl .r3a, false), [3, 4, 5], true, 7⟩, ⟨(.inl .r3b, false), [3, 4, 5], true, 7⟩, ⟨(.inl .r2d, false), [3, 4], true, 10⟩, ⟨(.inl .r2d, false), [3, 5], true, 11⟩,
      ⟨(.inl .r1b, false), [3], true, 12⟩, ⟨(.inl .r1b, false), [5], true, 11⟩, ⟨(.inl .r2b, false), [0, 1, 4], false, 10⟩, ⟨(.inl .r3c, true), [0, 1], true, 9⟩,
      ⟨(.inl .r2a, false), [0, 1, 4, 5], false, 8⟩, ⟨(.inl .r2a, false), [0, 1, 3, 5], false, 7⟩, ⟨(.inl .r3b, false), [0, 1, 5], true, 6⟩, ⟨(.inl .r5a, false), [0, 1, 2, 3, 4, 5], true, 4⟩,
      ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 3⟩]
  | true, true, true, false =>
    [⟨(.inl .r1b, false), [0], false, 4⟩, ⟨(.inl .r1c, false), [0, 3, 4, 5], false, 5⟩, ⟨(.inl .r1b, false), [3], false, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩,
      ⟨(.inl .r2b, false), [0, 1, 3], true, 1⟩, ⟨(.inl .r1a, false), [0, 2], false, 2⟩, ⟨(.inl .r2b, false), [0, 2, 3], false, 1⟩, ⟨(.inl .r3a, false), [0, 1, 2], true, 0⟩,
      ⟨(.inl .r3b, false), [0, 1, 2], true, 0⟩, ⟨(.inl .r1a, false), [2, 3], false, 2⟩, ⟨(.inl .r3c, false), [2, 3], true, 3⟩, ⟨(.inl .r3b, true), [1, 2, 3], true, 1⟩,
      ⟨(.inl .r3a, true), [0, 2, 3], false, 0⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], true, 1⟩, ⟨(.inl .r3c, false), [0, 2], true, 2⟩, ⟨(.inl .r1a, false), [4, 5], false, 2⟩,
      ⟨(.inl .r2b, false), [4, 5, 0], true, 3⟩, ⟨(.inl .r2e, false), [3, 1, 2, 4, 5], true, 9⟩, ⟨(.inl .r3d, true), [0, 1, 2, 4, 5], false, 8⟩, ⟨(.inl .r4a, false), [0, 2, 4, 5], true, 7⟩,
      ⟨(.inl .r3e, false), [0, 2, 3, 4, 5], true, 6⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 5⟩, ⟨(.inl .r4c, false), [2, 3, 4, 5], true, 4⟩, ⟨(.inl .r2a, false), [0, 2, 3, 5], false, 5⟩,
      ⟨(.inl .r3b, false), [2, 3, 5], true, 6⟩, ⟨(.inl .r3b, false), [2, 3, 5], false, 6⟩, ⟨(.inl .r3a, false), [2, 3, 5], false, 6⟩, ⟨(.inl .r1a, false), [2, 5], true, 7⟩,
      ⟨(.inl .r2b, false), [0, 1, 5], false, 8⟩, ⟨(.inl .r2b, false), [0, 1, 2], false, 7⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], false, 6⟩, ⟨(.inl .r3a, true), [0, 1, 2], true, 5⟩,
      ⟨(.inl .r2d, false), [3, 5], false, 9⟩, ⟨(.inl .r2d, false), [1, 5], false, 10⟩, ⟨(.inl .r2d, false), [1, 3], false, 9⟩, ⟨(.inl .r2d, false), [1, 2], false, 8⟩,
      ⟨(.inl .r2d, false), [2, 3], true, 9⟩, ⟨(.inl .r2d, false), [2, 5], true, 10⟩, ⟨(.inl .r1b, false), [2], true, 11⟩, ⟨(.inl .r3a, true), [0, 1, 2], false, 5⟩,
      ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inl .r3c, false), [0, 1], true, 7⟩, ⟨(.inl .r2b, false), [0, 1, 3], true, 8⟩, ⟨(.inl .r3a, true), [0, 2, 3], false, 5⟩,
      ⟨(.inl .r3c, true), [0, 2], false, 6⟩, ⟨(.inl .r2b, false), [0, 2, 3], true, 7⟩, ⟨(.inl .r2b, false), [0, 3, 2], true, 5⟩, ⟨(.inl .r3c, false), [0, 3], true, 6⟩,
      ⟨(.inl .r2d, false), [0, 2], false, 5⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 10⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 9⟩, ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 8⟩,
      ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .k22, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r2d, false), [1, 2], true, 9⟩, ⟨(.inl .r2d, false), [1, 3], true, 10⟩,
      ⟨(.inl .r2d, false), [2, 3], true, 9⟩, ⟨(.inl .r3c, false), [1, 3], false, 11⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 10⟩, ⟨(.inl .r3c, true), [1, 3], true, 9⟩,
      ⟨(.inl .r2b, false), [1, 3, 0], false, 8⟩, ⟨(.inl .r3b, true), [1, 2, 3], false, 7⟩, ⟨(.inl .r2b, false), [2, 3, 0], true, 8⟩, ⟨(.inl .r2b, false), [2, 3, 1], true, 9⟩,
      ⟨(.inl .r3c, true), [2, 3], false, 10⟩, ⟨(.inl .r3c, false), [2, 3], true, 11⟩, ⟨(.inl .r1a, false), [2, 3], true, 12⟩, ⟨(.inl .r2d, false), [2, 3], false, 10⟩,
      ⟨(.inl .r2d, false), [1, 2], true, 9⟩, ⟨(.inl .r2d, false), [1, 3], true, 10⟩, ⟨(.inl .r2d, false), [2, 3], true, 9⟩, ⟨(.inl .r3c, false), [1, 3], false, 11⟩,
      ⟨(.inl .r2b, false), [1, 3, 2], false, 10⟩, ⟨(.inl .r3c, true), [1, 3], true, 9⟩, ⟨(.inl .r2b, false), [1, 3, 0], false, 8⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 7⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], true, 7⟩, ⟨(.inl .r2d, false), [1, 2], true, 10⟩, ⟨(.inl .r2d, false), [1, 3], true, 11⟩, ⟨(.inl .r1b, false), [1], true, 12⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 11⟩, ⟨(.inl .r1b, false), [2], true, 10⟩, ⟨(.inl .r2b, false), [2, 3, 0], true, 8⟩, ⟨(.inl .r3c, false), [2, 3], true, 9⟩,
      ⟨(.inl .r1a, false), [2, 3], true, 10⟩, ⟨(.inl .r1b, false), [2], true, 9⟩, ⟨(.inl .r2b, false), [1, 3, 0], true, 7⟩, ⟨(.inl .r3c, false), [1, 3], true, 8⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 9⟩, ⟨(.inl .r1b, false), [1], true, 8⟩, ⟨(.inl .r2d, false), [0, 3], true, 7⟩, ⟨(.inl .r2d, false), [0, 5], true, 8⟩,
      ⟨(.inl .r1b, false), [0], true, 9⟩, ⟨(.inl .r2b, false), [0, 1, 3], true, 6⟩, ⟨(.inl .r2b, false), [0, 1, 5], true, 7⟩, ⟨(.inl .r3d, false), [0, 1, 3, 4, 5], true, 8⟩,
      ⟨(.inr .k21, false), [1, 3, 4, 5], true, 6⟩, ⟨(.inl .r2a, false), [0, 1, 4, 5], false, 8⟩, ⟨(.inl .r3b, false), [0, 1, 3], true, 7⟩, ⟨(.inl .r5a, false), [0, 1, 2, 3, 4, 5], true, 5⟩,
      ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 4⟩]
  | _, _, _, _ => []

theorem chk323_0312 : ∀ x y p q : Bool, xor (xor (xor x y) p) q = true →
    checkD (Gen.k 1 2 4 5 (by decide) (by decide) (by decide) :: (negw x 1 ++ negw y 2) ++ [Gen.k 0 1 2 3 (by decide) (by decide) (by decide)])
      (X323_0312 x y p q ++ Gen.k 0 1 2 4 (by decide) (by decide) (by decide) :: Y323_0312 x y p q ++
        Gen.k 0 3 4 5 (by decide) (by decide) (by decide) :: (negw p 0 ++ negw q 3)) (S323_0312 x y p q) = true := by
  decide +kernel

theorem tag323_0312 : ∀ x y p q : Bool, ∀ g ∈ X323_0312 x y p q ++ Y323_0312 x y p q, g.tag ≠ 2 := by
  decide

/-- Subcase 3.2.3 with `{a,b} = {0,3}`, `{α,β} = {1,2}` (from `0`). -/
theorem rel323_0312 {a0 a1 a2 a3 c d : Fin n} (h1 : a0 < a1) (h2 : a1 < a2) (h3 : a2 < a3) (h4 : a3 < c) (h5 : c < d) (x y p q : Bool)
    (hpar : xor (xor (xor x y) p) q = true) :
    ∃ Xw Yw : List (Gen n), (∀ g ∈ Xw ++ Yw, g.tag ≠ 2 ∧ extent g ≤ d.val) ∧
      Derivable (Table1 n)
        (FreeMonoid.ofList (Gen.k a1 a2 c d h2 (h3.trans h4) h5 :: (negw x a1 ++ negw y a2) ++
          [Gen.k a0 a1 a2 a3 h1 h2 h3]))
        (FreeMonoid.ofList (Xw ++ Gen.k a0 a1 a2 c h1 h2 (h3.trans h4) :: Yw ++
          Gen.k a0 a3 c d (h1.trans (h2.trans h3)) h4 h5 :: (negw p a0 ++ negw q a3))) := by
  refine ⟨(X323_0312 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)),
    (Y323_0312 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)), ?_, ?_⟩
  · intro g hg
    rw [← List.map_append] at hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    refine ⟨by rw [tag_rename]; exact tag323_0312 x y p q g' hg', ?_⟩
    have := extent_rename_le (emb6 h1 h2 h3 h4 h5) g' 5 (extent_le_last g')
    rwa [emb6_5] at this
  · have hh := derivable_rename (emb6 h1 h2 h3 h4 h5) (checkD_sound (chk323_0312 x y p q hpar))
    rw [renW_ofList, renW_ofList] at hh
    convert hh using 2 <;>
      simp only [List.map_append, List.map_cons, List.map_nil, negw_rename, Gen.rename, emb6_0,
        emb6_1, emb6_2, emb6_3, emb6_4, emb6_5, List.cons_append, List.nil_append,
        List.append_assoc]

/-- `X` for `{a,b} = {1,2}`, `{α,β} = {0,3}`. -/
def X323_1203 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, true => [Gen.x 0 2 (by decide)]
  | false, false, true, false => [Gen.x 0 1 (by decide)]
  | false, true, false, false => [Gen.x 0 2 (by decide), Gen.x 1 3 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide)]
  | false, true, true, true => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide)]
  | true, false, false, false => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 0, Gen.neg 2]
  | true, false, true, true => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide)]
  | true, true, false, true => [Gen.x 0 2 (by decide)]
  | true, true, true, false => [Gen.x 0 1 (by decide)]
  | _, _, _, _ => []

/-- `Y` for `{a,b} = {1,2}`, `{α,β} = {0,3}`. -/
def Y323_1203 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, true => [Gen.x 2 3 (by decide), Gen.neg 3]
  | false, false, true, false => [Gen.x 1 2 (by decide), Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.neg 2, Gen.neg 3, Gen.neg 5]
  | false, true, false, false => [Gen.x 1 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 3]
  | false, true, true, true => [Gen.x 1 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 1, Gen.neg 3, Gen.neg 4]
  | true, false, false, false => [Gen.x 1 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 4]
  | true, false, true, true => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 3]
  | true, true, false, true => [Gen.x 0 2 (by decide), Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.neg 2, Gen.neg 3, Gen.neg 5]
  | true, true, true, false => [Gen.x 0 1 (by decide), Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.neg 3]
  | _, _, _, _ => []

/-- The chains for `{a,b} = {1,2}`, `{α,β} = {0,3}`. -/
def S323_1203 : Bool → Bool → Bool → Bool → List (GStep ((Fam ⊕ MFam) × Bool) 6)
  | false, false, false, true =>
    [⟨(.inl .r1b, false), [2], false, 2⟩, ⟨(.inl .r1c, false), [1, 2, 4, 5], false, 3⟩, ⟨(.inl .r1a, false), [0, 2], false, 0⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 1⟩,
      ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inl .r2d, false), [2, 3], false, 5⟩, ⟨(.inl .r1b, false), [2], true, 4⟩, ⟨(.inl .r2e, false), [3, 1, 2, 4, 5], true, 4⟩,
      ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r5a, false), [0, 1, 2, 3, 4, 5], true, 2⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 1⟩]
  | false, false, true, false =>
    [⟨(.inl .r1b, false), [1], false, 2⟩, ⟨(.inl .r1c, false), [1, 2, 4, 5], false, 3⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩, ⟨(.inl .r3d, false), [0, 1, 3, 4, 5], true, 1⟩,
      ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inl .r2d, false), [1, 3], false, 5⟩, ⟨(.inl .r1b, false), [1], true, 4⟩, ⟨(.inl .r1a, false), [1, 2], false, 3⟩,
      ⟨(.inl .r3a, false), [1, 2, 3], true, 4⟩, ⟨(.inl .r2e, false), [3, 1, 2, 4, 5], true, 6⟩, ⟨(.inl .r4a, false), [1, 2, 4, 5], true, 5⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 4⟩,
      ⟨(.inl .r3d, false), [1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r3a, false), [2, 3, 5], true, 5⟩, ⟨(.inl .r3b, false), [2, 3, 5], true, 5⟩, ⟨(.inl .r2d, false), [3, 5], false, 8⟩,
      ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 1⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 2⟩]
  | false, true, false, false =>
    [⟨(.inl .r1c, false), [1, 2, 4, 5], false, 3⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩, ⟨(.inl .r1a, false), [0, 2], false, 1⟩, ⟨(.inl .r3a, false), [0, 1, 2], true, 0⟩,
      ⟨(.inl .r3b, false), [0, 1, 2], true, 0⟩, ⟨(.inl .r1a, false), [1, 3], false, 2⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 1⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 1⟩,
      ⟨(.inl .r1a, false), [4, 5], false, 3⟩, ⟨(.inl .r3d, false), [0, 1, 3, 4, 5], true, 7⟩, ⟨(.inl .r2c, false), [0, 2, 1, 3, 4, 5], true, 6⟩, ⟨(.inl .r4a, false), [1, 3, 4, 5], true, 5⟩,
      ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 4⟩, ⟨(.inl .r1a, false), [3, 5], true, 5⟩, ⟨(.inl .r2b, false), [0, 2, 5], false, 6⟩, ⟨(.inl .r2b, false), [0, 2, 3], false, 5⟩,
      ⟨(.inl .r2b, false), [0, 1, 5], false, 7⟩, ⟨(.inl .r2b, false), [0, 1, 3], false, 6⟩, ⟨(.inl .r3a, true), [0, 1, 2], true, 5⟩, ⟨(.inl .r2d, false), [3, 5], false, 8⟩,
      ⟨(.inl .r1b, false), [3], true, 7⟩, ⟨(.inl .r3a, true), [0, 1, 2], false, 5⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 7⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 6⟩,
      ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r2d, false), [2, 3], true, 7⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 8⟩, ⟨(.inl .r3c, true), [1, 3], true, 7⟩,
      ⟨(.inl .r3b, true), [1, 2, 3], false, 6⟩, ⟨(.inl .r2d, false), [1, 2], false, 9⟩, ⟨(.inl .r1b, false), [1], true, 8⟩, ⟨(.inl .r2d, false), [3, 5], true, 9⟩,
      ⟨(.inl .r3c, true), [2, 3], false, 7⟩, ⟨(.inl .r2b, false), [2, 3, 5], true, 8⟩, ⟨(.inl .r2b, false), [1, 2, 3], true, 6⟩, ⟨(.inl .r2b, false), [1, 2, 5], true, 7⟩,
      ⟨(.inl .r2e, false), [3, 1, 2, 4, 5], true, 10⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 9⟩, ⟨(.inl .r3d, false), [1, 2, 3, 4, 5], true, 8⟩, ⟨(.inr .k21, false), [2, 3, 4, 5], true, 6⟩,
      ⟨(.inl .r2a, false), [1, 2, 4, 5], false, 8⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 7⟩, ⟨(.inl .r2a, false), [2, 3, 4, 5], false, 9⟩, ⟨(.inl .r1a, false), [2, 3], true, 8⟩,
      ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 5⟩]
  | false, true, true, true =>
    [⟨(.inl .r1b, false), [2], false, 3⟩, ⟨(.inl .r1b, false), [1], false, 3⟩, ⟨(.inl .r2d, false), [1, 2], true, 4⟩, ⟨(.inl .r2d, false), [1, 2], true, 3⟩,
      ⟨(.inl .r1c, false), [1, 2, 4, 5], false, 5⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩, ⟨(.inl .r1a, false), [1, 3], false, 1⟩, ⟨(.inl .r1a, false), [4, 5], false, 2⟩,
      ⟨(.inl .r3d, false), [0, 1, 3, 4, 5], true, 5⟩, ⟨(.inl .r4a, false), [1, 3, 4, 5], true, 4⟩, ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 3⟩, ⟨(.inl .r1a, false), [3, 5], true, 4⟩,
      ⟨(.inl .r2b, false), [0, 1, 5], false, 5⟩, ⟨(.inl .r2b, false), [0, 1, 3], false, 4⟩, ⟨(.inl .r2d, false), [3, 5], false, 6⟩, ⟨(.inl .r1b, false), [3], true, 5⟩,
      ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 5⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r2d, false), [2, 5], false, 8⟩, ⟨(.inl .r2d, false), [2, 3], false, 7⟩,
      ⟨(.inl .r2d, false), [1, 2], true, 6⟩, ⟨(.inl .r2d, false), [1, 3], true, 7⟩, ⟨(.inl .r2d, false), [1, 5], true, 8⟩, ⟨(.inl .r1b, false), [1], true, 9⟩,
      ⟨(.inl .r2d, false), [3, 5], true, 7⟩, ⟨(.inl .r1a, false), [1, 2], false, 8⟩, ⟨(.inl .r2b, false), [1, 2, 5], false, 7⟩, ⟨(.inl .r3c, true), [1, 2], true, 6⟩,
      ⟨(.inl .r3a, true), [1, 2, 3], true, 5⟩, ⟨(.inl .r2e, false), [3, 1, 2, 4, 5], true, 10⟩, ⟨(.inl .r4a, false), [1, 2, 4, 5], true, 9⟩, ⟨(.inr .k32, false), [1, 2, 4, 5], true, 7⟩,
      ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 6⟩, ⟨(.inl .r3d, false), [1, 2, 3, 4, 5], true, 5⟩, ⟨(.inl .r3b, true), [1, 2, 3], true, 6⟩, ⟨(.inl .r3a, false), [1, 3, 5], true, 7⟩,
      ⟨(.inl .r3b, false), [1, 3, 5], true, 7⟩, ⟨(.inl .r2a, false), [1, 5, 2, 3], false, 6⟩, ⟨(.inl .r3b, true), [2, 3, 5], true, 7⟩, ⟨(.inl .r3a, true), [2, 4, 5], true, 8⟩,
      ⟨(.inl .r2a, false), [2, 4, 3, 5], false, 7⟩, ⟨(.inl .r3c, true), [2, 5], true, 13⟩, ⟨(.inl .r2b, false), [2, 5, 4], false, 12⟩, ⟨(.inl .r3c, false), [2, 5], false, 11⟩,
      ⟨(.inl .r2b, false), [2, 5, 1], false, 10⟩, ⟨(.inl .r3b, true), [2, 4, 5], false, 9⟩, ⟨(.inl .r2a, false), [2, 4, 3, 5], false, 8⟩, ⟨(.inl .r1a, false), [2, 4], true, 7⟩,
      ⟨(.inl .r2d, false), [4, 5], false, 10⟩, ⟨(.inl .r2d, false), [2, 5], false, 11⟩, ⟨(.inl .r2d, false), [2, 4], false, 10⟩, ⟨(.inl .r2d, false), [2, 4], true, 10⟩,
      ⟨(.inl .r2d, false), [2, 5], true, 11⟩, ⟨(.inl .r1b, false), [2], true, 12⟩, ⟨(.inl .r1b, false), [5], true, 11⟩, ⟨(.inl .r2d, false), [3, 4], false, 10⟩,
      ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 4⟩]
  | true, false, false, false =>
    [⟨(.inl .r1c, false), [1, 2, 4, 5], false, 3⟩, ⟨(.inl .r1b, false), [1], false, 0⟩, ⟨(.inl .r1b, false), [2], false, 1⟩, ⟨(.inl .r1a, false), [0, 1], false, 2⟩,
      ⟨(.inl .r2b, false), [0, 1, 2], false, 1⟩, ⟨(.inl .r3c, true), [0, 1], true, 0⟩, ⟨(.inl .r1a, false), [1, 3], false, 3⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 2⟩,
      ⟨(.inl .r2b, false), [1, 3, 0], false, 1⟩, ⟨(.inl .r1a, false), [4, 5], false, 4⟩, ⟨(.inl .r2b, false), [4, 5, 2], false, 3⟩, ⟨(.inl .r2b, false), [4, 5, 0], false, 2⟩,
      ⟨(.inl .r2e, false), [1, 0, 3, 4, 5], true, 9⟩, ⟨(.inl .r2e, false), [2, 0, 3, 4, 5], true, 8⟩, ⟨(.inl .r3d, false), [0, 1, 3, 4, 5], true, 7⟩, ⟨(.inl .r4a, false), [1, 3, 4, 5], true, 6⟩,
      ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 5⟩, ⟨(.inl .r1a, false), [3, 5], true, 6⟩, ⟨(.inl .r2b, false), [0, 1, 5], false, 7⟩, ⟨(.inl .r2b, false), [0, 1, 3], false, 6⟩,
      ⟨(.inl .r2d, false), [2, 5], false, 8⟩, ⟨(.inl .r2d, false), [2, 3], false, 7⟩, ⟨(.inl .r2d, false), [1, 5], false, 9⟩, ⟨(.inl .r2d, false), [1, 3], false, 8⟩,
      ⟨(.inl .r2d, false), [1, 2], false, 7⟩, ⟨(.inl .r2d, false), [0, 5], false, 10⟩, ⟨(.inl .r2d, false), [0, 3], false, 9⟩, ⟨(.inl .r2d, false), [0, 2], false, 8⟩,
      ⟨(.inl .r2d, false), [0, 1], false, 7⟩, ⟨(.inl .r3c, true), [0, 1], false, 6⟩, ⟨(.inl .r3c, false), [0, 1], true, 7⟩, ⟨(.inl .r2b, false), [0, 1, 2], true, 8⟩,
      ⟨(.inl .r2b, false), [0, 1, 3], true, 9⟩, ⟨(.inl .r2d, false), [0, 1], false, 6⟩, ⟨(.inl .r2d, false), [1, 2], true, 7⟩, ⟨(.inl .r2d, false), [1, 3], true, 8⟩,
      ⟨(.inl .r2d, false), [0, 2], true, 6⟩, ⟨(.inl .r2d, false), [0, 3], true, 7⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 11⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 10⟩,
      ⟨(.inr .k12, false), [0, 1, 2, 3], true, 8⟩, ⟨(.inr .k11, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], false, 8⟩, ⟨(.inl .r1a, false), [0, 2], true, 7⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 7⟩, ⟨(.inl .r2d, false), [1, 2], true, 8⟩, ⟨(.inl .r2d, false), [1, 3], true, 9⟩, ⟨(.inl .r2d, false), [2, 3], true, 8⟩,
      ⟨(.inl .r3c, false), [1, 3], false, 10⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 9⟩, ⟨(.inl .r3c, true), [1, 3], true, 8⟩, ⟨(.inl .r2b, false), [1, 3, 0], false, 7⟩,
      ⟨(.inl .r2d, false), [1, 2], true, 9⟩, ⟨(.inl .r2d, false), [1, 3], true, 10⟩, ⟨(.inl .r1b, false), [1], true, 11⟩, ⟨(.inl .r1b, false), [3], true, 10⟩,
      ⟨(.inl .r2d, false), [0, 2], true, 8⟩, ⟨(.inl .r2d, false), [0, 5], true, 9⟩, ⟨(.inl .r1a, false), [1, 2], false, 10⟩, ⟨(.inl .r2b, false), [1, 2, 5], false, 9⟩,
      ⟨(.inl .r3c, true), [1, 2], true, 8⟩, ⟨(.inl .r3a, true), [1, 2, 3], true, 7⟩, ⟨(.inl .r2e, false), [0, 1, 2, 4, 5], true, 12⟩, ⟨(.inl .r4a, false), [1, 2, 4, 5], true, 11⟩,
      ⟨(.inr .k32, false), [1, 2, 4, 5], true, 9⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 8⟩, ⟨(.inl .r3d, false), [1, 2, 3, 4, 5], true, 7⟩, ⟨(.inl .r3b, true), [1, 2, 3], true, 8⟩,
      ⟨(.inl .r3a, false), [1, 3, 5], true, 9⟩, ⟨(.inl .r3b, false), [1, 3, 5], true, 9⟩, ⟨(.inl .r2a, false), [1, 5, 2, 3], false, 8⟩, ⟨(.inl .r3b, true), [2, 3, 5], true, 9⟩,
      ⟨(.inl .r3a, true), [2, 4, 5], true, 10⟩, ⟨(.inl .r2a, false), [2, 4, 3, 5], false, 9⟩, ⟨(.inl .r3c, true), [2, 5], true, 15⟩, ⟨(.inl .r2b, false), [2, 5, 4], false, 14⟩,
      ⟨(.inl .r3c, false), [2, 5], false, 13⟩, ⟨(.inl .r2b, false), [2, 5, 1], false, 12⟩, ⟨(.inl .r3b, true), [2, 4, 5], false, 11⟩, ⟨(.inl .r2a, false), [2, 4, 3, 5], false, 10⟩,
      ⟨(.inl .r1a, false), [2, 4], true, 9⟩, ⟨(.inl .r2d, false), [4, 5], false, 12⟩, ⟨(.inl .r2d, false), [2, 5], false, 13⟩, ⟨(.inl .r2d, false), [2, 4], false, 12⟩,
      ⟨(.inl .r2d, false), [2, 4], true, 12⟩, ⟨(.inl .r2d, false), [2, 5], true, 13⟩, ⟨(.inl .r1b, false), [2], true, 14⟩, ⟨(.inl .r1b, false), [5], true, 13⟩,
      ⟨(.inl .r2d, false), [0, 4], false, 12⟩, ⟨(.inl .r2d, false), [0, 1], false, 11⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 5⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 6⟩]
  | true, false, true, true =>
    [⟨(.inl .r1b, false), [2], false, 3⟩, ⟨(.inl .r1b, false), [1], false, 3⟩, ⟨(.inl .r2d, false), [1, 2], true, 4⟩, ⟨(.inl .r2d, false), [1, 2], true, 3⟩,
      ⟨(.inl .r1c, false), [1, 2, 4, 5], false, 5⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩, ⟨(.inl .r1a, false), [1, 3], false, 1⟩, ⟨(.inl .r1a, false), [4, 5], false, 2⟩,
      ⟨(.inl .r3d, false), [0, 1, 3, 4, 5], true, 5⟩, ⟨(.inl .r4a, false), [1, 3, 4, 5], true, 4⟩, ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 3⟩, ⟨(.inl .r1a, false), [3, 5], true, 4⟩,
      ⟨(.inl .r2b, false), [0, 1, 5], false, 5⟩, ⟨(.inl .r2b, false), [0, 1, 3], false, 4⟩, ⟨(.inl .r2d, false), [0, 5], false, 6⟩, ⟨(.inl .r2d, false), [0, 3], false, 5⟩,
      ⟨(.inl .r3c, true), [0, 1], false, 4⟩, ⟨(.inl .r2b, false), [0, 1, 3], true, 5⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 7⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 6⟩,
      ⟨(.inr .k21, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r3b, true), [1, 2, 3], false, 6⟩, ⟨(.inl .r2d, false), [2, 5], false, 10⟩, ⟨(.inl .r2d, false), [2, 3], false, 9⟩,
      ⟨(.inl .r2d, false), [1, 2], true, 8⟩, ⟨(.inl .r2d, false), [1, 3], true, 9⟩, ⟨(.inl .r2d, false), [1, 5], true, 10⟩, ⟨(.inl .r1b, false), [1], true, 11⟩,
      ⟨(.inl .r2d, false), [3, 5], true, 9⟩, ⟨(.inl .r3a, true), [0, 1, 2], false, 5⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inl .r2b, false), [0, 1, 2], true, 7⟩,
      ⟨(.inl .r2b, false), [0, 1, 5], true, 8⟩, ⟨(.inl .r3c, true), [2, 3], false, 6⟩, ⟨(.inl .r2b, false), [2, 3, 5], true, 7⟩, ⟨(.inl .r2b, false), [0, 2, 3], true, 5⟩,
      ⟨(.inl .r2b, false), [0, 2, 5], true, 6⟩, ⟨(.inl .r2e, false), [3, 1, 2, 4, 5], true, 10⟩, ⟨(.inl .r3d, true), [0, 1, 2, 4, 5], false, 9⟩, ⟨(.inl .r3e, false), [0, 2, 3, 4, 5], true, 8⟩,
      ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 7⟩, ⟨(.inr .k21, false), [2, 3, 4, 5], true, 5⟩, ⟨(.inl .r2a, false), [0, 2, 4, 5], false, 7⟩, ⟨(.inl .r3b, false), [0, 2, 3], true, 6⟩,
      ⟨(.inl .r2a, false), [2, 3, 4, 5], false, 8⟩, ⟨(.inl .r1a, false), [2, 3], true, 7⟩, ⟨(.inl .r2a, false), [0, 1, 4, 5], false, 7⟩, ⟨(.inl .r3a, true), [0, 1, 3], true, 6⟩,
      ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 4⟩]
  | true, true, false, true =>
    [⟨(.inl .r1b, false), [2], false, 4⟩, ⟨(.inl .r1c, false), [1, 2, 4, 5], false, 5⟩, ⟨(.inl .r1a, false), [0, 2], false, 0⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 1⟩,
      ⟨(.inl .r3c, true), [0, 2], false, 2⟩, ⟨(.inl .r2b, false), [0, 2, 3], true, 3⟩, ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inr .k11, false), [0, 1, 2, 3], true, 2⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 7⟩, ⟨(.inl .r1b, false), [2], true, 6⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], true, 3⟩, ⟨(.inl .r3b, true), [0, 2, 3], true, 4⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], false, 3⟩, ⟨(.inl .r2e, false), [3, 1, 2, 4, 5], true, 6⟩, ⟨(.inl .r2c, false), [0, 3, 1, 2, 4, 5], true, 5⟩, ⟨(.inl .r4a, false), [1, 2, 4, 5], true, 4⟩,
      ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r3a, false), [2, 3, 5], true, 4⟩, ⟨(.inl .r3b, false), [2, 3, 5], true, 4⟩, ⟨(.inl .r2b, false), [0, 3, 5], false, 7⟩,
      ⟨(.inl .r2b, false), [0, 3, 2], false, 6⟩, ⟨(.inl .r3b, false), [0, 3, 5], true, 5⟩, ⟨(.inl .r3b, true), [0, 2, 5], false, 4⟩, ⟨(.inl .r2d, false), [3, 5], false, 8⟩,
      ⟨(.inl .r5a, false), [0, 1, 2, 3, 4, 5], true, 2⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 1⟩]
  | true, true, true, false =>
    [⟨(.inl .r1b, false), [1], false, 4⟩, ⟨(.inl .r1c, false), [1, 2, 4, 5], false, 5⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩, ⟨(.inl .r3d, false), [0, 1, 3, 4, 5], true, 1⟩,
      ⟨(.inl .r3c, true), [0, 1], false, 2⟩, ⟨(.inl .r2b, false), [0, 1, 3], true, 3⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inr .k21, false), [0, 1, 2, 3], true, 2⟩,
      ⟨(.inl .r3b, true), [1, 2, 3], false, 4⟩, ⟨(.inl .r2d, false), [1, 3], false, 7⟩, ⟨(.inl .r1b, false), [1], true, 6⟩, ⟨(.inl .r3a, true), [0, 1, 2], false, 3⟩,
      ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r2e, false), [3, 1, 2, 4, 5], true, 6⟩, ⟨(.inl .r3d, true), [0, 1, 2, 4, 5], false, 5⟩, ⟨(.inl .r3e, false), [0, 2, 3, 4, 5], true, 4⟩,
      ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], false, 5⟩, ⟨(.inl .r3a, true), [0, 1, 2], true, 4⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 1⟩,
      ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 2⟩]
  | _, _, _, _ => []

theorem chk323_1203 : ∀ x y p q : Bool, xor (xor (xor x y) p) q = true →
    checkD (Gen.k 0 3 4 5 (by decide) (by decide) (by decide) :: (negw x 0 ++ negw y 3) ++ [Gen.k 0 1 2 3 (by decide) (by decide) (by decide)])
      (X323_1203 x y p q ++ Gen.k 0 1 2 4 (by decide) (by decide) (by decide) :: Y323_1203 x y p q ++
        Gen.k 1 2 4 5 (by decide) (by decide) (by decide) :: (negw p 1 ++ negw q 2)) (S323_1203 x y p q) = true := by
  decide +kernel

theorem tag323_1203 : ∀ x y p q : Bool, ∀ g ∈ X323_1203 x y p q ++ Y323_1203 x y p q, g.tag ≠ 2 := by
  decide

/-- Subcase 3.2.3 with `{a,b} = {1,2}`, `{α,β} = {0,3}` (from `0`). -/
theorem rel323_1203 {a0 a1 a2 a3 c d : Fin n} (h1 : a0 < a1) (h2 : a1 < a2) (h3 : a2 < a3) (h4 : a3 < c) (h5 : c < d) (x y p q : Bool)
    (hpar : xor (xor (xor x y) p) q = true) :
    ∃ Xw Yw : List (Gen n), (∀ g ∈ Xw ++ Yw, g.tag ≠ 2 ∧ extent g ≤ d.val) ∧
      Derivable (Table1 n)
        (FreeMonoid.ofList (Gen.k a0 a3 c d (h1.trans (h2.trans h3)) h4 h5 :: (negw x a0 ++ negw y a3) ++
          [Gen.k a0 a1 a2 a3 h1 h2 h3]))
        (FreeMonoid.ofList (Xw ++ Gen.k a0 a1 a2 c h1 h2 (h3.trans h4) :: Yw ++
          Gen.k a1 a2 c d h2 (h3.trans h4) h5 :: (negw p a1 ++ negw q a2))) := by
  refine ⟨(X323_1203 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)),
    (Y323_1203 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)), ?_, ?_⟩
  · intro g hg
    rw [← List.map_append] at hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    refine ⟨by rw [tag_rename]; exact tag323_1203 x y p q g' hg', ?_⟩
    have := extent_rename_le (emb6 h1 h2 h3 h4 h5) g' 5 (extent_le_last g')
    rwa [emb6_5] at this
  · have hh := derivable_rename (emb6 h1 h2 h3 h4 h5) (checkD_sound (chk323_1203 x y p q hpar))
    rw [renW_ofList, renW_ofList] at hh
    convert hh using 2 <;>
      simp only [List.map_append, List.map_cons, List.map_nil, negw_rename, Gen.rename, emb6_0,
        emb6_1, emb6_2, emb6_3, emb6_4, emb6_5, List.cons_append, List.nil_append,
        List.append_assoc]

/-- `X` for `{a,b} = {1,2}`, `{α,β} = {1,2}`. -/
def X323_1212 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, false => [Gen.x 2 3 (by decide)]
  | false, false, true, true => [Gen.x 0 3 (by decide), Gen.x 2 3 (by decide)]
  | false, true, false, true => [Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide)]
  | false, true, true, false => [Gen.x 0 3 (by decide), Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide)]
  | true, false, false, true => [Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide)]
  | true, false, true, false => [Gen.x 1 5 (by decide), Gen.x 2 3 (by decide), Gen.x 3 4 (by decide)]
  | true, true, false, false => [Gen.x 2 3 (by decide)]
  | true, true, true, true => [Gen.x 0 3 (by decide), Gen.x 2 3 (by decide)]
  | _, _, _, _ => []

/-- `Y` for `{a,b} = {1,2}`, `{α,β} = {1,2}`. -/
def Y323_1212 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, false => [Gen.x 1 2 (by decide), Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.neg 2, Gen.neg 5]
  | false, false, true, true => [Gen.x 1 2 (by decide), Gen.x 2 3 (by decide)]
  | false, true, false, true => [Gen.x 1 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 1, Gen.neg 4]
  | false, true, true, false => [Gen.x 1 3 (by decide), Gen.x 4 5 (by decide)]
  | true, false, false, true => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide)]
  | true, false, true, false => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 1, Gen.neg 2, Gen.neg 4, Gen.neg 5]
  | true, true, false, false => [Gen.x 0 1 (by decide), Gen.x 1 2 (by decide), Gen.x 2 3 (by decide)]
  | true, true, true, true => [Gen.x 0 1 (by decide), Gen.x 1 2 (by decide), Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.neg 2, Gen.neg 5]
  | _, _, _, _ => []

/-- The chains for `{a,b} = {1,2}`, `{α,β} = {1,2}`. -/
def S323_1212 : Bool → Bool → Bool → Bool → List (GStep ((Fam ⊕ MFam) × Bool) 6)
  | false, false, false, false =>
    [⟨(.inl .r1c, false), [1, 2, 4, 5], false, 2⟩, ⟨(.inl .r1a, false), [2, 3], false, 0⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 1⟩, ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 2⟩,
      ⟨(.inl .r1a, false), [1, 2], false, 3⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 4⟩, ⟨(.inl .r4a, false), [1, 2, 4, 5], true, 5⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 4⟩,
      ⟨(.inl .r3d, false), [1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r3a, false), [2, 3, 5], true, 5⟩, ⟨(.inl .r3b, false), [2, 3, 5], true, 5⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 1⟩,
      ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 2⟩]
  | false, false, true, true =>
    [⟨(.inl .r1b, false), [2], false, 2⟩, ⟨(.inl .r1b, false), [1], false, 2⟩, ⟨(.inl .r2d, false), [1, 2], true, 3⟩, ⟨(.inl .r2d, false), [1, 2], true, 2⟩,
      ⟨(.inl .r1c, false), [1, 2, 4, 5], false, 4⟩, ⟨(.inl .r1a, false), [0, 3], false, 0⟩, ⟨(.inl .r1a, false), [2, 3], false, 1⟩, ⟨(.inl .r2c, false), [0, 3, 1, 2, 4, 5], true, 3⟩,
      ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 2⟩, ⟨(.inl .r3b, true), [0, 2, 3], false, 3⟩, ⟨(.inl .r3a, true), [0, 2, 3], false, 3⟩, ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 4⟩,
      ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 3⟩, ⟨(.inl .r3b, false), [1, 2, 3], false, 4⟩, ⟨(.inl .r3a, false), [1, 2, 3], false, 4⟩, ⟨(.inl .r1a, false), [1, 3], true, 5⟩,
      ⟨(.inl .r3c, false), [2, 3], false, 6⟩, ⟨(.inl .r2b, false), [2, 3, 1], false, 5⟩, ⟨(.inl .r2d, false), [2, 3], false, 7⟩, ⟨(.inl .r1b, false), [3], true, 8⟩,
      ⟨(.inl .r1b, false), [2], true, 7⟩, ⟨(.inl .r1b, false), [1], true, 6⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 5⟩, ⟨(.inl .r3d, false), [1, 2, 3, 4, 5], true, 4⟩,
      ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 2⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 3⟩]
  | false, true, false, true =>
    [⟨(.inl .r1b, false), [2], false, 3⟩, ⟨(.inl .r1c, false), [1, 2, 4, 5], false, 4⟩, ⟨(.inl .r1a, false), [1, 2], false, 0⟩, ⟨(.inl .r1a, false), [2, 3], false, 1⟩,
      ⟨(.inl .r1a, false), [4, 5], false, 2⟩, ⟨(.inl .r4a, false), [1, 2, 4, 5], true, 5⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 3⟩,
      ⟨(.inl .r3b, false), [2, 3, 5], true, 4⟩, ⟨(.inl .r3b, false), [2, 3, 5], false, 4⟩, ⟨(.inl .r3a, false), [2, 3, 5], false, 4⟩, ⟨(.inl .r1a, false), [2, 5], true, 5⟩,
      ⟨(.inl .r2d, false), [2, 5], false, 6⟩, ⟨(.inl .r1b, false), [2], true, 5⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 5⟩, ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 4⟩,
      ⟨(.inl .r2d, false), [2, 5], false, 6⟩, ⟨(.inl .r1a, false), [1, 2], false, 8⟩, ⟨(.inl .r2b, false), [1, 2, 5], false, 7⟩, ⟨(.inl .r3c, true), [1, 2], true, 6⟩,
      ⟨(.inl .r3a, true), [1, 2, 3], true, 5⟩, ⟨(.inl .r4a, false), [1, 2, 4, 5], true, 9⟩, ⟨(.inr .k32, false), [1, 2, 4, 5], true, 7⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 6⟩,
      ⟨(.inl .r3d, false), [1, 2, 3, 4, 5], true, 5⟩, ⟨(.inl .r3b, true), [1, 2, 3], true, 6⟩, ⟨(.inl .r3a, false), [1, 3, 5], true, 7⟩, ⟨(.inl .r3b, false), [1, 3, 5], true, 7⟩,
      ⟨(.inl .r2a, false), [1, 5, 2, 3], false, 6⟩, ⟨(.inl .r3b, true), [2, 3, 5], true, 7⟩, ⟨(.inl .r3a, true), [2, 4, 5], true, 8⟩, ⟨(.inl .r2a, false), [2, 4, 3, 5], false, 7⟩,
      ⟨(.inl .r3c, true), [2, 5], true, 13⟩, ⟨(.inl .r2b, false), [2, 5, 4], false, 12⟩, ⟨(.inl .r3c, false), [2, 5], false, 11⟩, ⟨(.inl .r2b, false), [2, 5, 1], false, 10⟩,
      ⟨(.inl .r3b, true), [2, 4, 5], false, 9⟩, ⟨(.inl .r2a, false), [2, 4, 3, 5], false, 8⟩, ⟨(.inl .r1a, false), [2, 4], true, 7⟩, ⟨(.inl .r2d, false), [4, 5], false, 10⟩,
      ⟨(.inl .r2d, false), [2, 5], false, 11⟩, ⟨(.inl .r2d, false), [2, 4], false, 10⟩, ⟨(.inl .r2d, false), [2, 4], true, 10⟩, ⟨(.inl .r2d, false), [2, 5], true, 11⟩,
      ⟨(.inl .r1b, false), [2], true, 12⟩, ⟨(.inl .r1b, false), [5], true, 11⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 4⟩]
  | false, true, true, false =>
    [⟨(.inl .r1b, false), [1], false, 3⟩, ⟨(.inl .r1c, false), [1, 2, 4, 5], false, 4⟩, ⟨(.inl .r1a, false), [0, 3], false, 0⟩, ⟨(.inl .r1a, false), [1, 2], false, 1⟩,
      ⟨(.inl .r1a, false), [2, 3], false, 2⟩, ⟨(.inl .r1a, false), [4, 5], false, 3⟩, ⟨(.inl .r2c, false), [0, 3, 1, 2, 4, 5], true, 7⟩, ⟨(.inl .r4a, false), [1, 2, 4, 5], true, 6⟩,
      ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 5⟩, ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 4⟩, ⟨(.inl .r3b, false), [2, 3, 5], true, 5⟩, ⟨(.inl .r3b, false), [2, 3, 5], false, 5⟩,
      ⟨(.inl .r3a, false), [2, 3, 5], false, 5⟩, ⟨(.inl .r1a, false), [2, 5], true, 6⟩, ⟨(.inl .r2b, false), [0, 3, 5], false, 7⟩, ⟨(.inl .r2b, false), [0, 3, 2], false, 6⟩,
      ⟨(.inl .r3b, true), [0, 2, 3], false, 5⟩, ⟨(.inl .r2d, false), [2, 5], false, 8⟩, ⟨(.inl .r1b, false), [2], true, 7⟩, ⟨(.inl .r3a, true), [0, 2, 3], false, 5⟩,
      ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 7⟩, ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r3b, false), [1, 2, 3], false, 6⟩,
      ⟨(.inl .r3a, false), [1, 2, 3], false, 6⟩, ⟨(.inl .r1a, false), [1, 3], true, 7⟩, ⟨(.inl .r3c, false), [2, 3], false, 8⟩, ⟨(.inl .r2b, false), [2, 3, 1], false, 7⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 9⟩, ⟨(.inl .r1b, false), [3], true, 10⟩, ⟨(.inl .r2d, false), [1, 2], true, 8⟩, ⟨(.inl .r2d, false), [1, 5], true, 9⟩,
      ⟨(.inl .r1b, false), [1], true, 10⟩, ⟨(.inl .r3c, true), [2, 3], false, 7⟩, ⟨(.inl .r2b, false), [2, 3, 5], true, 8⟩, ⟨(.inl .r2b, false), [1, 2, 3], true, 6⟩,
      ⟨(.inl .r2b, false), [1, 2, 5], true, 7⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 9⟩, ⟨(.inl .r3d, false), [1, 2, 3, 4, 5], true, 8⟩, ⟨(.inr .k21, false), [2, 3, 4, 5], true, 6⟩,
      ⟨(.inl .r2a, false), [1, 2, 4, 5], false, 8⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 7⟩, ⟨(.inl .r2a, false), [2, 3, 4, 5], false, 9⟩, ⟨(.inl .r1a, false), [2, 3], true, 8⟩,
      ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 5⟩]
  | true, false, false, true =>
    [⟨(.inl .r1b, false), [2], false, 3⟩, ⟨(.inl .r1c, false), [1, 2, 4, 5], false, 4⟩, ⟨(.inl .r1a, false), [1, 2], false, 0⟩, ⟨(.inl .r1a, false), [2, 3], false, 1⟩,
      ⟨(.inl .r1a, false), [4, 5], false, 2⟩, ⟨(.inl .r4a, false), [1, 2, 4, 5], true, 5⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 3⟩,
      ⟨(.inl .r3b, false), [2, 3, 5], true, 4⟩, ⟨(.inl .r3b, false), [2, 3, 5], false, 4⟩, ⟨(.inl .r3a, false), [2, 3, 5], false, 4⟩, ⟨(.inl .r1a, false), [2, 5], true, 5⟩,
      ⟨(.inl .r2d, false), [1, 5], false, 6⟩, ⟨(.inl .r2d, false), [1, 2], false, 5⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 7⟩, ⟨(.inr .k31, false), [0, 1, 2, 3], true, 5⟩,
      ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r3b, true), [0, 1, 3], false, 5⟩, ⟨(.inl .r3a, true), [1, 2, 3], true, 6⟩, ⟨(.inl .r2d, false), [2, 5], false, 8⟩,
      ⟨(.inl .r3a, true), [0, 1, 2], false, 5⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inl .r2b, false), [0, 1, 2], true, 7⟩, ⟨(.inl .r2b, false), [0, 1, 5], true, 8⟩,
      ⟨(.inl .r3c, true), [2, 3], false, 6⟩, ⟨(.inl .r2b, false), [2, 3, 5], true, 7⟩, ⟨(.inl .r2b, false), [0, 2, 3], true, 5⟩, ⟨(.inl .r2b, false), [0, 2, 5], true, 6⟩,
      ⟨(.inl .r3d, true), [0, 1, 2, 4, 5], false, 9⟩, ⟨(.inl .r3e, false), [0, 2, 3, 4, 5], true, 8⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 7⟩, ⟨(.inr .k21, false), [2, 3, 4, 5], true, 5⟩,
      ⟨(.inl .r2a, false), [0, 2, 4, 5], false, 7⟩, ⟨(.inl .r3b, false), [0, 2, 3], true, 6⟩, ⟨(.inl .r2a, false), [2, 3, 4, 5], false, 8⟩, ⟨(.inl .r1a, false), [2, 3], true, 7⟩,
      ⟨(.inl .r2a, false), [0, 1, 4, 5], false, 7⟩, ⟨(.inl .r3a, true), [0, 1, 3], true, 6⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 4⟩]
  | true, false, true, false =>
    [⟨(.inl .r1b, false), [1], false, 3⟩, ⟨(.inl .r1c, false), [1, 2, 4, 5], false, 4⟩, ⟨(.inl .r1a, false), [1, 5], false, 0⟩, ⟨(.inl .r1a, false), [2, 3], false, 1⟩,
      ⟨(.inl .r1a, false), [3, 4], false, 2⟩, ⟨(.inr .ksym5, false), [1, 2, 4, 5], true, 5⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 4⟩, ⟨(.inr .ksym2, false), [1, 3, 4, 5], true, 3⟩,
      ⟨(.inl .r3b, false), [2, 3, 4], true, 4⟩, ⟨(.inl .r2a, false), [2, 5, 3, 4], false, 5⟩, ⟨(.inl .r3a, false), [2, 4, 5], true, 4⟩, ⟨(.inl .r3b, false), [2, 4, 5], true, 4⟩,
      ⟨(.inl .r3b, false), [3, 4, 5], true, 5⟩, ⟨(.inl .r1a, false), [4, 5], true, 6⟩, ⟨(.inl .r3b, false), [2, 3, 5], false, 4⟩, ⟨(.inl .r3a, false), [2, 3, 5], false, 4⟩,
      ⟨(.inl .r1a, false), [2, 5], true, 5⟩, ⟨(.inl .r2d, false), [1, 4], false, 6⟩, ⟨(.inl .r2d, false), [1, 2], false, 5⟩, ⟨(.inl .r2e, false), [4, 0, 1, 2, 3], true, 7⟩,
      ⟨(.inr .k31, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r3b, true), [0, 1, 3], false, 5⟩, ⟨(.inl .r3a, true), [1, 2, 3], true, 6⟩,
      ⟨(.inl .r2d, false), [1, 4], false, 8⟩, ⟨(.inl .r3a, true), [0, 1, 2], false, 5⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inl .r3c, false), [0, 1], true, 7⟩,
      ⟨(.inl .r2b, false), [0, 1, 4], true, 8⟩, ⟨(.inl .r3d, true), [0, 1, 2, 4, 5], false, 9⟩, ⟨(.inr .k22, false), [0, 2, 4, 5], true, 7⟩, ⟨(.inl .r3e, false), [0, 2, 3, 4, 5], true, 6⟩,
      ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 5⟩, ⟨(.inl .r3a, false), [0, 2, 3], false, 7⟩, ⟨(.inl .r1a, false), [0, 2], true, 6⟩, ⟨(.inl .r2b, false), [0, 1, 5], false, 11⟩,
      ⟨(.inl .r2b, false), [0, 1, 4], false, 10⟩, ⟨(.inl .r2b, false), [0, 1, 2], false, 9⟩, ⟨(.inl .r3c, false), [0, 1], false, 8⟩, ⟨(.inl .r2a, false), [0, 1, 4, 5], false, 7⟩,
      ⟨(.inl .r3a, true), [0, 1, 3], true, 6⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 4⟩]
  | true, true, false, false =>
    [⟨(.inl .r1c, false), [1, 2, 4, 5], false, 4⟩, ⟨(.inl .r1a, false), [2, 3], false, 0⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 1⟩, ⟨(.inr .k31, false), [0, 1, 2, 3], true, 3⟩,
      ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inl .r3b, true), [0, 1, 3], false, 3⟩, ⟨(.inl .r3a, true), [1, 2, 3], true, 4⟩, ⟨(.inl .r3a, true), [0, 1, 2], false, 3⟩,
      ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r3d, true), [0, 1, 2, 4, 5], false, 5⟩, ⟨(.inl .r3e, false), [0, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 3⟩,
      ⟨(.inl .r2a, false), [0, 1, 2, 3], false, 5⟩, ⟨(.inl .r3a, true), [0, 1, 2], true, 4⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 1⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 2⟩]
  | true, true, true, true =>
    [⟨(.inl .r1b, false), [2], false, 4⟩, ⟨(.inl .r1b, false), [1], false, 4⟩, ⟨(.inl .r2d, false), [1, 2], true, 5⟩, ⟨(.inl .r2d, false), [1, 2], true, 4⟩,
      ⟨(.inl .r1c, false), [1, 2, 4, 5], false, 6⟩, ⟨(.inl .r1a, false), [0, 3], false, 0⟩, ⟨(.inl .r1a, false), [2, 3], false, 1⟩, ⟨(.inl .r2c, false), [0, 3, 1, 2, 4, 5], true, 3⟩,
      ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 2⟩, ⟨(.inl .r3b, true), [0, 2, 3], false, 3⟩, ⟨(.inl .r3a, true), [0, 2, 3], false, 3⟩, ⟨(.inl .r2b, false), [0, 2, 1], true, 4⟩,
      ⟨(.inl .r3c, false), [0, 2], true, 5⟩, ⟨(.inl .r2d, false), [0, 1], false, 4⟩, ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 4⟩,
      ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 3⟩, ⟨(.inl .r3b, false), [1, 2, 3], false, 4⟩, ⟨(.inl .r3a, false), [1, 2, 3], false, 4⟩, ⟨(.inl .r1a, false), [1, 3], true, 5⟩,
      ⟨(.inl .r2d, false), [1, 2], true, 5⟩, ⟨(.inl .r2b, false), [0, 2, 1], false, 6⟩, ⟨(.inl .r3c, true), [0, 2], true, 5⟩, ⟨(.inl .r3b, true), [0, 1, 2], false, 4⟩,
      ⟨(.inl .r3c, false), [1, 3], false, 7⟩, ⟨(.inl .r2b, false), [1, 3, 0], false, 6⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 5⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 5⟩,
      ⟨(.inl .r2d, false), [0, 3], false, 8⟩, ⟨(.inl .r1b, false), [0], true, 7⟩, ⟨(.inl .r2d, false), [1, 3], false, 7⟩, ⟨(.inl .r2d, false), [2, 3], false, 8⟩,
      ⟨(.inl .r1b, false), [3], true, 9⟩, ⟨(.inl .r2b, false), [2, 3, 1], true, 6⟩, ⟨(.inl .r3c, true), [2, 3], false, 7⟩, ⟨(.inl .r1a, false), [2, 3], true, 8⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 7⟩, ⟨(.inl .r1b, false), [3], true, 8⟩, ⟨(.inl .r1b, false), [2], true, 7⟩, ⟨(.inl .r1b, false), [1], true, 6⟩,
      ⟨(.inl .r3a, true), [0, 1, 3], false, 4⟩, ⟨(.inl .r1a, false), [0, 2], false, 4⟩, ⟨(.inl .r3a, false), [0, 2, 3], true, 5⟩, ⟨(.inl .r3d, true), [0, 1, 2, 4, 5], false, 7⟩,
      ⟨(.inl .r4a, false), [0, 2, 4, 5], true, 6⟩, ⟨(.inl .r3e, false), [0, 2, 3, 4, 5], true, 5⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r3a, false), [2, 3, 5], true, 6⟩,
      ⟨(.inl .r3b, false), [2, 3, 5], true, 6⟩, ⟨(.inl .r2b, false), [0, 1, 5], false, 9⟩, ⟨(.inl .r2b, false), [0, 1, 2], false, 8⟩, ⟨(.inl .r2a, false), [0, 1, 3, 5], false, 7⟩,
      ⟨(.inl .r2a, false), [0, 1, 2, 5], false, 6⟩, ⟨(.inl .r3a, true), [0, 1, 2], true, 5⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 2⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 3⟩]
  | _, _, _, _ => []

theorem chk323_1212 : ∀ x y p q : Bool, xor (xor (xor x y) p) q = false →
    checkD (Gen.k 1 2 4 5 (by decide) (by decide) (by decide) :: (negw x 1 ++ negw y 2) ++ [Gen.k 0 1 2 3 (by decide) (by decide) (by decide)])
      (X323_1212 x y p q ++ Gen.k 0 1 2 4 (by decide) (by decide) (by decide) :: Y323_1212 x y p q ++
        Gen.k 1 2 4 5 (by decide) (by decide) (by decide) :: (negw p 1 ++ negw q 2)) (S323_1212 x y p q) = true := by
  decide +kernel

theorem tag323_1212 : ∀ x y p q : Bool, ∀ g ∈ X323_1212 x y p q ++ Y323_1212 x y p q, g.tag ≠ 2 := by
  decide

/-- Subcase 3.2.3 with `{a,b} = {1,2}`, `{α,β} = {1,2}` (from `0`). -/
theorem rel323_1212 {a0 a1 a2 a3 c d : Fin n} (h1 : a0 < a1) (h2 : a1 < a2) (h3 : a2 < a3) (h4 : a3 < c) (h5 : c < d) (x y p q : Bool)
    (hpar : xor (xor (xor x y) p) q = false) :
    ∃ Xw Yw : List (Gen n), (∀ g ∈ Xw ++ Yw, g.tag ≠ 2 ∧ extent g ≤ d.val) ∧
      Derivable (Table1 n)
        (FreeMonoid.ofList (Gen.k a1 a2 c d h2 (h3.trans h4) h5 :: (negw x a1 ++ negw y a2) ++
          [Gen.k a0 a1 a2 a3 h1 h2 h3]))
        (FreeMonoid.ofList (Xw ++ Gen.k a0 a1 a2 c h1 h2 (h3.trans h4) :: Yw ++
          Gen.k a1 a2 c d h2 (h3.trans h4) h5 :: (negw p a1 ++ negw q a2))) := by
  refine ⟨(X323_1212 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)),
    (Y323_1212 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)), ?_, ?_⟩
  · intro g hg
    rw [← List.map_append] at hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    refine ⟨by rw [tag_rename]; exact tag323_1212 x y p q g' hg', ?_⟩
    have := extent_rename_le (emb6 h1 h2 h3 h4 h5) g' 5 (extent_le_last g')
    rwa [emb6_5] at this
  · have hh := derivable_rename (emb6 h1 h2 h3 h4 h5) (checkD_sound (chk323_1212 x y p q hpar))
    rw [renW_ofList, renW_ofList] at hh
    convert hh using 2 <;>
      simp only [List.map_append, List.map_cons, List.map_nil, negw_rename, Gen.rename, emb6_0,
        emb6_1, emb6_2, emb6_3, emb6_4, emb6_5, List.cons_append, List.nil_append,
        List.append_assoc]

/-- `X` for `{a,b} = {1,3}`, `{α,β} = {0,1}`. -/
def X323_1301 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, true => [Gen.x 0 2 (by decide), Gen.x 1 3 (by decide)]
  | false, false, true, false => [Gen.x 0 3 (by decide), Gen.x 1 3 (by decide)]
  | false, true, false, false => [Gen.x 0 2 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide)]
  | false, true, true, true => [Gen.x 0 3 (by decide), Gen.x 4 5 (by decide)]
  | true, false, false, false => [Gen.x 0 2 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide)]
  | true, false, true, true => [Gen.x 0 3 (by decide), Gen.x 4 5 (by decide)]
  | true, true, false, true => [Gen.x 0 2 (by decide), Gen.x 1 3 (by decide)]
  | true, true, true, false => [Gen.x 0 3 (by decide), Gen.x 1 3 (by decide)]
  | _, _, _, _ => []

/-- `Y` for `{a,b} = {1,3}`, `{α,β} = {0,1}`. -/
def Y323_1301 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, true => [Gen.neg 2]
  | false, false, true, false => [Gen.x 1 2 (by decide), Gen.x 3 5 (by decide), Gen.neg 2, Gen.neg 3, Gen.neg 5]
  | false, true, false, false => [Gen.x 1 3 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 2]
  | false, true, true, true => [Gen.x 1 5 (by decide), Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 1, Gen.neg 2, Gen.neg 4]
  | true, false, false, false => [Gen.x 0 1 (by decide), Gen.x 1 5 (by decide), Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 1, Gen.neg 2, Gen.neg 4]
  | true, false, true, true => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 2]
  | true, true, false, true => [Gen.x 0 2 (by decide), Gen.x 3 5 (by decide), Gen.neg 2, Gen.neg 3, Gen.neg 5]
  | true, true, true, false => [Gen.x 0 1 (by decide), Gen.x 1 2 (by decide), Gen.neg 2]
  | _, _, _, _ => []

/-- The chains for `{a,b} = {1,3}`, `{α,β} = {0,1}`. -/
def S323_1301 : Bool → Bool → Bool → Bool → List (GStep ((Fam ⊕ MFam) × Bool) 6)
  | false, false, false, true =>
    [⟨(.inl .r1b, false), [3], false, 2⟩, ⟨(.inl .r1c, false), [1, 3, 4, 5], false, 3⟩, ⟨(.inl .r1a, false), [1, 3], false, 0⟩, ⟨(.inl .r1a, false), [0, 2], false, 0⟩,
      ⟨(.inl .r2a, false), [0, 2, 1, 3], true, 1⟩, ⟨(.inl .r3e, false), [0, 1, 3, 4, 5], true, 3⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 2⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], true, 3⟩,
      ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inr .ksym6, false), [0, 1, 2, 3], true, 3⟩, ⟨(.inl .r1a, false), [2, 3], true, 4⟩, ⟨(.inl .r1b, false), [3], true, 5⟩,
      ⟨(.inl .r2e, false), [2, 1, 3, 4, 5], true, 4⟩, ⟨(.inl .r5a, false), [0, 1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 2⟩]
  | false, false, true, false =>
    [⟨(.inl .r1b, false), [1], false, 2⟩, ⟨(.inl .r1c, false), [1, 3, 4, 5], false, 3⟩, ⟨(.inl .r1a, false), [1, 3], false, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 1⟩,
      ⟨(.inl .r3b, false), [0, 1, 3], true, 0⟩, ⟨(.inl .r3e, false), [0, 1, 3, 4, 5], true, 3⟩, ⟨(.inl .r3d, false), [0, 1, 3, 4, 5], true, 2⟩, ⟨(.inl .r3a, true), [0, 1, 3], false, 3⟩,
      ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 3⟩, ⟨(.inl .r3b, false), [1, 2, 3], false, 4⟩, ⟨(.inl .r3a, false), [1, 2, 3], false, 4⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 5⟩, ⟨(.inl .r2d, false), [1, 2], true, 5⟩, ⟨(.inl .r3c, false), [1, 3], false, 6⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 5⟩,
      ⟨(.inl .r3a, false), [1, 2, 3], true, 4⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 4⟩, ⟨(.inl .r2d, false), [1, 3], false, 7⟩, ⟨(.inl .r2d, false), [1, 2], false, 6⟩,
      ⟨(.inl .r1b, false), [3], true, 8⟩, ⟨(.inl .r2d, false), [1, 2], false, 7⟩, ⟨(.inl .r1b, false), [1], true, 6⟩, ⟨(.inl .r3b, false), [1, 2, 3], false, 4⟩,
      ⟨(.inl .r2e, false), [2, 1, 3, 4, 5], true, 6⟩, ⟨(.inl .r3d, false), [1, 2, 3, 4, 5], true, 5⟩, ⟨(.inl .r4a, false), [2, 3, 4, 5], true, 4⟩, ⟨(.inl .r2b, false), [1, 2, 5], false, 7⟩,
      ⟨(.inl .r2b, false), [1, 2, 3], false, 6⟩, ⟨(.inl .r2a, false), [1, 2, 3, 5], false, 5⟩, ⟨(.inl .r2d, false), [2, 5], false, 8⟩, ⟨(.inl .r2d, false), [2, 3], false, 7⟩,
      ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 2⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 3⟩]
  | false, true, false, false =>
    [⟨(.inl .r1c, false), [1, 3, 4, 5], false, 3⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩, ⟨(.inl .r1a, false), [1, 2], false, 1⟩, ⟨(.inl .r3a, true), [0, 1, 2], false, 0⟩,
      ⟨(.inl .r1a, false), [2, 3], false, 1⟩, ⟨(.inl .r1a, false), [4, 5], false, 2⟩, ⟨(.inl .r4a, false), [0, 1, 4, 5], true, 7⟩, ⟨(.inl .r3e, false), [0, 1, 2, 4, 5], true, 6⟩,
      ⟨(.inl .r3d, false), [0, 1, 2, 4, 5], true, 5⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 3⟩, ⟨(.inl .r3b, false), [2, 3, 5], true, 4⟩,
      ⟨(.inl .r2a, false), [0, 1, 3, 5], false, 5⟩, ⟨(.inl .r2a, false), [0, 1, 2, 5], false, 4⟩, ⟨(.inl .r2a, false), [1, 2, 3, 5], false, 6⟩, ⟨(.inl .r3b, false), [1, 2, 5], true, 5⟩,
      ⟨(.inl .r3b, false), [2, 3, 5], false, 6⟩, ⟨(.inl .r2a, false), [1, 5, 2, 3], false, 7⟩, ⟨(.inl .r3b, true), [1, 3, 5], false, 6⟩, ⟨(.inl .r3a, true), [1, 3, 5], false, 6⟩,
      ⟨(.inl .r1a, false), [1, 5], true, 5⟩, ⟨(.inl .r2d, false), [1, 5], false, 8⟩, ⟨(.inl .r1b, false), [1], true, 7⟩, ⟨(.inl .r3a, true), [0, 1, 3], false, 4⟩,
      ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r3b, false), [0, 2, 3], false, 4⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 7⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 6⟩,
      ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r3c, true), [1, 3], true, 8⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 7⟩,
      ⟨(.inl .r3b, true), [1, 2, 3], false, 6⟩, ⟨(.inl .r3a, true), [1, 2, 3], false, 6⟩, ⟨(.inl .r1a, false), [1, 3], true, 5⟩, ⟨(.inl .r2d, false), [1, 2], false, 6⟩,
      ⟨(.inl .r2d, false), [1, 2], false, 7⟩, ⟨(.inl .r1b, false), [1], true, 6⟩, ⟨(.inl .r2d, false), [2, 3], true, 6⟩, ⟨(.inl .r2d, false), [2, 5], true, 7⟩,
      ⟨(.inl .r2b, false), [1, 2, 3], true, 5⟩, ⟨(.inl .r2b, false), [1, 2, 5], true, 6⟩, ⟨(.inl .r2e, false), [2, 1, 3, 4, 5], true, 8⟩, ⟨(.inl .r3d, false), [1, 2, 3, 4, 5], true, 7⟩,
      ⟨(.inr .k21, false), [2, 3, 4, 5], true, 5⟩, ⟨(.inl .r2a, false), [1, 2, 4, 5], false, 7⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 6⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 3⟩,
      ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 4⟩]
  | false, true, true, true =>
    [⟨(.inl .r1b, false), [3], false, 3⟩, ⟨(.inl .r1b, false), [1], false, 3⟩, ⟨(.inl .r2d, false), [1, 3], true, 4⟩, ⟨(.inl .r2d, false), [1, 3], true, 3⟩,
      ⟨(.inl .r1c, false), [1, 3, 4, 5], false, 5⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩, ⟨(.inl .r1a, false), [1, 3], false, 1⟩, ⟨(.inl .r3a, true), [0, 1, 3], false, 0⟩,
      ⟨(.inl .r1a, false), [4, 5], false, 1⟩, ⟨(.inl .r4a, false), [0, 1, 4, 5], true, 5⟩, ⟨(.inl .r3e, false), [0, 1, 3, 4, 5], true, 4⟩, ⟨(.inl .r3d, false), [0, 1, 3, 4, 5], true, 3⟩,
      ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 2⟩, ⟨(.inl .r2a, false), [0, 1, 3, 5], false, 3⟩, ⟨(.inl .r3b, false), [1, 3, 5], true, 4⟩, ⟨(.inl .r3b, false), [1, 3, 5], false, 4⟩,
      ⟨(.inl .r3a, false), [1, 3, 5], false, 4⟩, ⟨(.inl .r1a, false), [1, 5], true, 5⟩, ⟨(.inl .r2d, false), [1, 5], false, 6⟩, ⟨(.inl .r1b, false), [1], true, 5⟩,
      ⟨(.inl .r3a, true), [0, 1, 3], false, 3⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 5⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 3⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], false, 4⟩, ⟨(.inl .r3a, false), [1, 2, 3], false, 4⟩, ⟨(.inl .r1a, false), [1, 3], true, 5⟩, ⟨(.inl .r2d, false), [1, 2], true, 5⟩,
      ⟨(.inl .r3c, false), [1, 3], false, 6⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 5⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 4⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 4⟩,
      ⟨(.inl .r2d, false), [1, 3], false, 7⟩, ⟨(.inl .r2d, false), [1, 2], false, 6⟩, ⟨(.inl .r1b, false), [3], true, 8⟩, ⟨(.inl .r2d, false), [3, 5], false, 8⟩,
      ⟨(.inl .r2d, false), [1, 2], true, 6⟩, ⟨(.inl .r2d, false), [1, 3], true, 7⟩, ⟨(.inl .r2d, false), [1, 5], true, 8⟩, ⟨(.inl .r1b, false), [1], true, 9⟩,
      ⟨(.inl .r2d, false), [2, 3], true, 6⟩, ⟨(.inl .r2d, false), [2, 5], true, 7⟩, ⟨(.inl .r3b, false), [1, 2, 3], false, 4⟩, ⟨(.inl .r2b, false), [1, 2, 3], true, 5⟩,
      ⟨(.inl .r2b, false), [1, 2, 5], true, 6⟩, ⟨(.inl .r3c, false), [2, 3], true, 4⟩, ⟨(.inl .r2b, false), [2, 3, 5], true, 5⟩, ⟨(.inl .r2e, false), [2, 1, 3, 4, 5], true, 8⟩,
      ⟨(.inl .r3d, false), [1, 2, 3, 4, 5], true, 7⟩, ⟨(.inl .r4a, false), [2, 3, 4, 5], true, 6⟩, ⟨(.inr .k32, false), [2, 3, 4, 5], true, 4⟩, ⟨(.inl .r2d, false), [3, 4], true, 8⟩,
      ⟨(.inl .r2d, false), [3, 5], true, 9⟩, ⟨(.inl .r2d, false), [4, 5], true, 8⟩, ⟨(.inl .r3c, false), [3, 5], false, 10⟩, ⟨(.inl .r2b, false), [3, 5, 4], false, 9⟩,
      ⟨(.inl .r3c, true), [3, 5], true, 8⟩, ⟨(.inl .r2b, false), [3, 5, 2], false, 7⟩, ⟨(.inl .r3a, false), [3, 4, 5], true, 6⟩, ⟨(.inl .r3b, false), [3, 4, 5], true, 6⟩,
      ⟨(.inl .r2d, false), [3, 4], true, 9⟩, ⟨(.inl .r2d, false), [3, 5], true, 10⟩, ⟨(.inl .r1b, false), [3], true, 11⟩, ⟨(.inl .r1b, false), [5], true, 10⟩,
      ⟨(.inl .r2b, false), [1, 2, 4], false, 9⟩, ⟨(.inl .r3c, true), [1, 2], true, 8⟩, ⟨(.inl .r2a, false), [1, 2, 4, 5], false, 7⟩, ⟨(.inl .r2a, false), [1, 2, 3, 5], false, 6⟩,
      ⟨(.inl .r3b, false), [1, 2, 5], true, 5⟩, ⟨(.inl .r2d, false), [2, 4], false, 10⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 2⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 3⟩]
  | true, false, false, false =>
    [⟨(.inl .r1c, false), [1, 3, 4, 5], false, 3⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩, ⟨(.inl .r1a, false), [1, 2], false, 1⟩, ⟨(.inl .r3a, true), [0, 1, 2], false, 0⟩,
      ⟨(.inl .r1a, false), [2, 3], false, 1⟩, ⟨(.inl .r1a, false), [4, 5], false, 2⟩, ⟨(.inl .r4a, false), [0, 1, 4, 5], true, 7⟩, ⟨(.inl .r3e, false), [0, 1, 2, 4, 5], true, 6⟩,
      ⟨(.inl .r3d, false), [0, 1, 2, 4, 5], true, 5⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 3⟩, ⟨(.inl .r3b, false), [2, 3, 5], true, 4⟩,
      ⟨(.inl .r2a, false), [0, 1, 3, 5], false, 5⟩, ⟨(.inl .r2a, false), [0, 1, 2, 5], false, 4⟩, ⟨(.inl .r2a, false), [1, 2, 3, 5], false, 6⟩, ⟨(.inl .r3b, false), [1, 2, 5], true, 5⟩,
      ⟨(.inl .r3b, false), [2, 3, 5], false, 6⟩, ⟨(.inl .r2a, false), [1, 5, 2, 3], false, 7⟩, ⟨(.inl .r3b, true), [1, 3, 5], false, 6⟩, ⟨(.inl .r3a, true), [1, 3, 5], false, 6⟩,
      ⟨(.inl .r1a, false), [1, 5], true, 5⟩, ⟨(.inl .r2d, false), [0, 5], false, 8⟩, ⟨(.inl .r2d, false), [0, 1], false, 7⟩, ⟨(.inl .r3a, true), [0, 1, 3], false, 4⟩,
      ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r3c, true), [0, 1], false, 6⟩, ⟨(.inl .r3c, false), [0, 1], true, 7⟩, ⟨(.inl .r2d, false), [0, 1], false, 6⟩,
      ⟨(.inl .r3b, false), [0, 2, 3], false, 4⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 9⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 8⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 6⟩,
      ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r2b, false), [0, 2, 3], false, 8⟩, ⟨(.inl .r3c, true), [0, 2], true, 7⟩,
      ⟨(.inl .r3b, false), [0, 2, 3], true, 6⟩, ⟨(.inl .r3b, true), [0, 1, 3], false, 5⟩, ⟨(.inl .r3c, true), [1, 3], true, 9⟩, ⟨(.inl .r2b, false), [1, 3, 0], false, 8⟩,
      ⟨(.inl .r3b, true), [1, 2, 3], false, 7⟩, ⟨(.inl .r3a, true), [1, 2, 3], false, 7⟩, ⟨(.inl .r1a, false), [1, 3], true, 6⟩, ⟨(.inl .r2d, false), [0, 1], false, 8⟩,
      ⟨(.inl .r1b, false), [0], true, 7⟩, ⟨(.inl .r1b, false), [1], true, 7⟩, ⟨(.inl .r2d, false), [2, 3], true, 7⟩, ⟨(.inl .r2b, false), [1, 3, 2], false, 8⟩,
      ⟨(.inl .r3c, true), [1, 3], true, 7⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 6⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 6⟩, ⟨(.inl .r2d, false), [1, 2], false, 9⟩,
      ⟨(.inl .r1b, false), [1], true, 8⟩, ⟨(.inl .r2d, false), [2, 3], true, 8⟩, ⟨(.inl .r2d, false), [2, 5], true, 9⟩, ⟨(.inl .r3a, true), [0, 1, 3], false, 5⟩,
      ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inl .r2b, false), [0, 1, 3], true, 7⟩, ⟨(.inl .r2b, false), [0, 1, 5], true, 8⟩, ⟨(.inl .r3b, false), [0, 2, 3], false, 5⟩,
      ⟨(.inl .r2b, false), [0, 2, 3], true, 6⟩, ⟨(.inl .r2b, false), [0, 2, 5], true, 7⟩, ⟨(.inl .r3c, false), [2, 3], true, 5⟩, ⟨(.inl .r2b, false), [2, 3, 5], true, 6⟩,
      ⟨(.inl .r2e, false), [2, 1, 3, 4, 5], true, 10⟩, ⟨(.inl .r3d, true), [0, 1, 3, 4, 5], false, 9⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 8⟩, ⟨(.inl .r4a, false), [2, 3, 4, 5], true, 7⟩,
      ⟨(.inr .k32, false), [2, 3, 4, 5], true, 5⟩, ⟨(.inl .r2d, false), [3, 4], true, 9⟩, ⟨(.inl .r2d, false), [3, 5], true, 10⟩, ⟨(.inl .r2d, false), [4, 5], true, 9⟩,
      ⟨(.inl .r3c, false), [3, 5], false, 11⟩, ⟨(.inl .r2b, false), [3, 5, 4], false, 10⟩, ⟨(.inl .r3c, true), [3, 5], true, 9⟩, ⟨(.inl .r2b, false), [3, 5, 2], false, 8⟩,
      ⟨(.inl .r3a, false), [3, 4, 5], true, 7⟩, ⟨(.inl .r3b, false), [3, 4, 5], true, 7⟩, ⟨(.inl .r2d, false), [3, 4], true, 10⟩, ⟨(.inl .r2d, false), [3, 5], true, 11⟩,
      ⟨(.inl .r1b, false), [3], true, 12⟩, ⟨(.inl .r1b, false), [5], true, 11⟩, ⟨(.inl .r2b, false), [0, 2, 4], false, 10⟩, ⟨(.inl .r3c, true), [0, 2], true, 9⟩,
      ⟨(.inl .r2a, false), [0, 2, 4, 5], false, 8⟩, ⟨(.inl .r2a, false), [0, 2, 3, 5], false, 7⟩, ⟨(.inl .r3b, false), [0, 2, 5], true, 6⟩, ⟨(.inl .r2b, false), [0, 1, 4], false, 11⟩,
      ⟨(.inl .r3c, false), [0, 1], false, 10⟩, ⟨(.inl .r2a, false), [0, 1, 4, 5], false, 9⟩, ⟨(.inl .r2a, false), [0, 1, 3, 5], false, 8⟩, ⟨(.inl .r2a, false), [0, 1, 2, 5], false, 7⟩,
      ⟨(.inl .r3a, true), [0, 1, 5], true, 6⟩, ⟨(.inl .r2d, false), [2, 4], false, 12⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 4⟩]
  | true, false, true, true =>
    [⟨(.inl .r1b, false), [3], false, 3⟩, ⟨(.inl .r1b, false), [1], false, 3⟩, ⟨(.inl .r2d, false), [1, 3], true, 4⟩, ⟨(.inl .r2d, false), [1, 3], true, 3⟩,
      ⟨(.inl .r1c, false), [1, 3, 4, 5], false, 5⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩, ⟨(.inl .r1a, false), [1, 3], false, 1⟩, ⟨(.inl .r3a, true), [0, 1, 3], false, 0⟩,
      ⟨(.inl .r1a, false), [4, 5], false, 1⟩, ⟨(.inl .r4a, false), [0, 1, 4, 5], true, 5⟩, ⟨(.inl .r3e, false), [0, 1, 3, 4, 5], true, 4⟩, ⟨(.inl .r3d, false), [0, 1, 3, 4, 5], true, 3⟩,
      ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 2⟩, ⟨(.inl .r2a, false), [0, 1, 3, 5], false, 3⟩, ⟨(.inl .r3b, false), [1, 3, 5], true, 4⟩, ⟨(.inl .r3b, false), [1, 3, 5], false, 4⟩,
      ⟨(.inl .r3a, false), [1, 3, 5], false, 4⟩, ⟨(.inl .r1a, false), [1, 5], true, 5⟩, ⟨(.inl .r2d, false), [0, 5], false, 6⟩, ⟨(.inl .r2d, false), [0, 1], false, 5⟩,
      ⟨(.inl .r3a, true), [0, 1, 3], false, 3⟩, ⟨(.inl .r3c, true), [0, 1], false, 4⟩, ⟨(.inl .r3c, false), [0, 1], true, 5⟩, ⟨(.inl .r2d, false), [0, 1], false, 4⟩,
      ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 7⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 3⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], false, 4⟩, ⟨(.inl .r3a, false), [1, 2, 3], false, 4⟩, ⟨(.inl .r1a, false), [1, 3], true, 5⟩, ⟨(.inl .r2d, false), [1, 2], true, 5⟩,
      ⟨(.inl .r2b, false), [0, 2, 1], false, 6⟩, ⟨(.inl .r3c, true), [0, 2], true, 5⟩, ⟨(.inl .r3b, true), [0, 1, 2], false, 4⟩, ⟨(.inl .r3c, false), [1, 3], false, 7⟩,
      ⟨(.inl .r2b, false), [1, 3, 0], false, 6⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 5⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 5⟩, ⟨(.inl .r2d, false), [0, 3], false, 8⟩,
      ⟨(.inl .r1b, false), [0], true, 7⟩, ⟨(.inl .r2d, false), [1, 3], false, 7⟩, ⟨(.inl .r2d, false), [2, 3], false, 8⟩, ⟨(.inl .r1b, false), [3], true, 9⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], false, 5⟩, ⟨(.inl .r3a, false), [1, 2, 3], false, 5⟩, ⟨(.inl .r3c, true), [1, 3], false, 6⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 7⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 8⟩, ⟨(.inl .r2d, false), [2, 3], false, 6⟩, ⟨(.inl .r2d, false), [1, 3], false, 7⟩, ⟨(.inl .r2d, false), [1, 2], false, 6⟩,
      ⟨(.inl .r1b, false), [3], true, 8⟩, ⟨(.inl .r2d, false), [3, 5], false, 8⟩, ⟨(.inl .r2d, false), [1, 2], true, 6⟩, ⟨(.inl .r2d, false), [1, 3], true, 7⟩,
      ⟨(.inl .r2d, false), [1, 5], true, 8⟩, ⟨(.inl .r1b, false), [1], true, 9⟩, ⟨(.inl .r2d, false), [2, 3], true, 6⟩, ⟨(.inl .r2d, false), [2, 5], true, 7⟩,
      ⟨(.inl .r3a, true), [0, 1, 2], false, 4⟩, ⟨(.inl .r2b, false), [0, 1, 3], true, 5⟩, ⟨(.inl .r2b, false), [0, 1, 5], true, 6⟩, ⟨(.inl .r2b, false), [0, 2, 3], true, 4⟩,
      ⟨(.inl .r2b, false), [0, 2, 5], true, 5⟩, ⟨(.inl .r2e, false), [2, 1, 3, 4, 5], true, 8⟩, ⟨(.inl .r3d, true), [0, 1, 3, 4, 5], false, 7⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 6⟩,
      ⟨(.inr .k21, false), [2, 3, 4, 5], true, 4⟩, ⟨(.inl .r2a, false), [0, 2, 4, 5], false, 6⟩, ⟨(.inl .r3b, false), [0, 2, 3], true, 5⟩, ⟨(.inl .r2a, false), [0, 1, 4, 5], false, 7⟩,
      ⟨(.inl .r2a, false), [0, 1, 2, 3], false, 6⟩, ⟨(.inl .r3a, true), [0, 1, 3], true, 5⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 2⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 3⟩]
  | true, true, false, true =>
    [⟨(.inl .r1b, false), [3], false, 4⟩, ⟨(.inl .r1c, false), [1, 3, 4, 5], false, 5⟩, ⟨(.inl .r1a, false), [1, 3], false, 0⟩, ⟨(.inl .r1a, false), [0, 2], false, 0⟩,
      ⟨(.inl .r2a, false), [0, 2, 1, 3], true, 1⟩, ⟨(.inl .r3e, false), [0, 1, 3, 4, 5], true, 3⟩, ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 2⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], true, 3⟩,
      ⟨(.inr .k12, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inr .ksym6, false), [0, 1, 2, 3], true, 3⟩, ⟨(.inl .r1a, false), [2, 3], true, 4⟩,
      ⟨(.inl .r2b, false), [0, 2, 3], false, 5⟩, ⟨(.inl .r3c, true), [0, 2], true, 4⟩, ⟨(.inl .r3c, true), [1, 3], true, 6⟩, ⟨(.inl .r2b, false), [1, 3, 0], false, 5⟩,
      ⟨(.inl .r2d, false), [0, 1], false, 7⟩, ⟨(.inl .r1b, false), [0], true, 6⟩, ⟨(.inl .r1b, false), [1], true, 6⟩, ⟨(.inl .r1b, false), [3], true, 7⟩,
      ⟨(.inl .r2a, false), [0, 2, 1, 3], true, 4⟩, ⟨(.inl .r2e, false), [2, 1, 3, 4, 5], true, 6⟩, ⟨(.inl .r2c, false), [0, 2, 1, 3, 4, 5], true, 5⟩, ⟨(.inl .r4a, false), [1, 3, 4, 5], true, 4⟩,
      ⟨(.inl .r2b, false), [0, 2, 5], false, 7⟩, ⟨(.inl .r2b, false), [0, 2, 3], false, 6⟩, ⟨(.inl .r2a, false), [0, 2, 3, 5], false, 5⟩, ⟨(.inl .r2d, false), [2, 5], false, 8⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 7⟩, ⟨(.inl .r5a, false), [0, 1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 2⟩]
  | true, true, true, false =>
    [⟨(.inl .r1b, false), [1], false, 4⟩, ⟨(.inl .r1c, false), [1, 3, 4, 5], false, 5⟩, ⟨(.inl .r1a, false), [1, 3], false, 0⟩, ⟨(.inl .r1a, false), [0, 1], false, 1⟩,
      ⟨(.inl .r3b, false), [0, 1, 3], true, 0⟩, ⟨(.inl .r3e, false), [0, 1, 3, 4, 5], true, 3⟩, ⟨(.inl .r3d, false), [0, 1, 3, 4, 5], true, 2⟩, ⟨(.inl .r3a, true), [0, 1, 3], false, 3⟩,
      ⟨(.inl .r3c, true), [0, 1], false, 4⟩, ⟨(.inl .r3c, false), [0, 1], true, 5⟩, ⟨(.inl .r2d, false), [0, 1], false, 4⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 6⟩,
      ⟨(.inr .k12, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 3⟩, ⟨(.inl .r3b, false), [1, 2, 3], false, 4⟩, ⟨(.inl .r3a, false), [1, 2, 3], false, 4⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 5⟩, ⟨(.inl .r2d, false), [1, 2], true, 5⟩, ⟨(.inl .r2b, false), [0, 2, 1], false, 6⟩, ⟨(.inl .r3c, true), [0, 2], true, 5⟩,
      ⟨(.inl .r3b, true), [0, 1, 2], false, 4⟩, ⟨(.inl .r3c, false), [1, 3], false, 7⟩, ⟨(.inl .r2b, false), [1, 3, 0], false, 6⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 5⟩,
      ⟨(.inl .r3b, false), [1, 2, 3], true, 5⟩, ⟨(.inl .r2d, false), [0, 3], false, 8⟩, ⟨(.inl .r1b, false), [0], true, 7⟩, ⟨(.inl .r2d, false), [1, 3], false, 7⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 8⟩, ⟨(.inl .r1b, false), [3], true, 9⟩, ⟨(.inl .r3b, false), [1, 2, 3], false, 5⟩, ⟨(.inl .r3a, false), [1, 2, 3], false, 5⟩,
      ⟨(.inl .r3c, true), [1, 3], false, 6⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 7⟩, ⟨(.inl .r1a, false), [1, 3], true, 8⟩, ⟨(.inl .r2d, false), [2, 3], false, 6⟩,
      ⟨(.inl .r2d, false), [1, 3], false, 7⟩, ⟨(.inl .r2d, false), [1, 2], false, 6⟩, ⟨(.inl .r1b, false), [3], true, 8⟩, ⟨(.inl .r2d, false), [1, 2], false, 7⟩,
      ⟨(.inl .r1b, false), [1], true, 6⟩, ⟨(.inl .r3a, true), [0, 1, 2], false, 4⟩, ⟨(.inl .r2e, false), [2, 1, 3, 4, 5], true, 6⟩, ⟨(.inl .r3d, true), [0, 1, 3, 4, 5], false, 5⟩,
      ⟨(.inl .r3d, false), [0, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r3a, true), [0, 1, 2], true, 5⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 2⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 3⟩]
  | _, _, _, _ => []

theorem chk323_1301 : ∀ x y p q : Bool, xor (xor (xor x y) p) q = true →
    checkD (Gen.k 0 1 4 5 (by decide) (by decide) (by decide) :: (negw x 0 ++ negw y 1) ++ [Gen.k 0 1 2 3 (by decide) (by decide) (by decide)])
      (X323_1301 x y p q ++ Gen.k 0 1 2 4 (by decide) (by decide) (by decide) :: Y323_1301 x y p q ++
        Gen.k 1 3 4 5 (by decide) (by decide) (by decide) :: (negw p 1 ++ negw q 3)) (S323_1301 x y p q) = true := by
  decide +kernel

theorem tag323_1301 : ∀ x y p q : Bool, ∀ g ∈ X323_1301 x y p q ++ Y323_1301 x y p q, g.tag ≠ 2 := by
  decide

/-- Subcase 3.2.3 with `{a,b} = {1,3}`, `{α,β} = {0,1}` (from `0`). -/
theorem rel323_1301 {a0 a1 a2 a3 c d : Fin n} (h1 : a0 < a1) (h2 : a1 < a2) (h3 : a2 < a3) (h4 : a3 < c) (h5 : c < d) (x y p q : Bool)
    (hpar : xor (xor (xor x y) p) q = true) :
    ∃ Xw Yw : List (Gen n), (∀ g ∈ Xw ++ Yw, g.tag ≠ 2 ∧ extent g ≤ d.val) ∧
      Derivable (Table1 n)
        (FreeMonoid.ofList (Gen.k a0 a1 c d h1 (h2.trans (h3.trans h4)) h5 :: (negw x a0 ++ negw y a1) ++
          [Gen.k a0 a1 a2 a3 h1 h2 h3]))
        (FreeMonoid.ofList (Xw ++ Gen.k a0 a1 a2 c h1 h2 (h3.trans h4) :: Yw ++
          Gen.k a1 a3 c d (h2.trans h3) h4 h5 :: (negw p a1 ++ negw q a3))) := by
  refine ⟨(X323_1301 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)),
    (Y323_1301 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)), ?_, ?_⟩
  · intro g hg
    rw [← List.map_append] at hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    refine ⟨by rw [tag_rename]; exact tag323_1301 x y p q g' hg', ?_⟩
    have := extent_rename_le (emb6 h1 h2 h3 h4 h5) g' 5 (extent_le_last g')
    rwa [emb6_5] at this
  · have hh := derivable_rename (emb6 h1 h2 h3 h4 h5) (checkD_sound (chk323_1301 x y p q hpar))
    rw [renW_ofList, renW_ofList] at hh
    convert hh using 2 <;>
      simp only [List.map_append, List.map_cons, List.map_nil, negw_rename, Gen.rename, emb6_0,
        emb6_1, emb6_2, emb6_3, emb6_4, emb6_5, List.cons_append, List.nil_append,
        List.append_assoc]

/-- `X` for `{a,b} = {1,3}`, `{α,β} = {2,3}`. -/
def X323_1323 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, false => []
  | false, false, true, true => [Gen.x 0 1 (by decide)]
  | false, true, false, true => [Gen.x 2 3 (by decide), Gen.x 4 5 (by decide)]
  | false, true, true, false => [Gen.x 2 3 (by decide), Gen.x 4 5 (by decide)]
  | true, false, false, true => [Gen.x 2 3 (by decide), Gen.x 4 5 (by decide)]
  | true, false, true, false => [Gen.x 0 1 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide)]
  | true, true, false, false => []
  | true, true, true, true => [Gen.x 0 1 (by decide)]
  | _, _, _, _ => []

/-- `Y` for `{a,b} = {1,3}`, `{α,β} = {2,3}`. -/
def Y323_1323 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, false => []
  | false, false, true, true => [Gen.x 3 5 (by decide), Gen.neg 3, Gen.neg 5]
  | false, true, false, true => [Gen.x 1 3 (by decide), Gen.x 4 5 (by decide)]
  | false, true, true, false => [Gen.x 1 5 (by decide), Gen.x 3 4 (by decide), Gen.neg 1, Gen.neg 3, Gen.neg 4, Gen.neg 5]
  | true, false, false, true => [Gen.x 0 2 (by decide), Gen.x 1 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 1, Gen.neg 4]
  | true, false, true, false => [Gen.x 0 2 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide)]
  | true, true, false, false => [Gen.x 0 2 (by decide), Gen.x 3 5 (by decide), Gen.neg 3, Gen.neg 5]
  | true, true, true, true => [Gen.x 0 2 (by decide)]
  | _, _, _, _ => []

/-- The chains for `{a,b} = {1,3}`, `{α,β} = {2,3}`. -/
def S323_1323 : Bool → Bool → Bool → Bool → List (GStep ((Fam ⊕ MFam) × Bool) 6)
  | false, false, false, false =>
    [⟨(.inl .r1c, false), [1, 3, 4, 5], false, 2⟩, ⟨(.inl .r5a, false), [0, 1, 2, 3, 4, 5], true, 1⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 0⟩]
  | false, false, true, true =>
    [⟨(.inl .r1b, false), [3], false, 2⟩, ⟨(.inl .r1b, false), [1], false, 2⟩, ⟨(.inl .r2d, false), [1, 3], true, 3⟩, ⟨(.inl .r2d, false), [1, 3], true, 2⟩,
      ⟨(.inl .r1c, false), [1, 3, 4, 5], false, 4⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩, ⟨(.inl .r2c, false), [0, 1, 2, 3, 4, 5], true, 1⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 2⟩,
      ⟨(.inl .r1b, false), [3], true, 5⟩, ⟨(.inl .r1b, false), [1], true, 4⟩, ⟨(.inl .r4a, false), [1, 3, 4, 5], true, 3⟩, ⟨(.inl .r5a, false), [0, 1, 2, 3, 4, 5], true, 2⟩,
      ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 1⟩]
  | false, true, false, true =>
    [⟨(.inl .r1b, false), [3], false, 3⟩, ⟨(.inl .r1c, false), [1, 3, 4, 5], false, 4⟩, ⟨(.inl .r1a, false), [2, 3], false, 0⟩, ⟨(.inl .r1a, false), [4, 5], false, 1⟩,
      ⟨(.inl .r4a, false), [2, 3, 4, 5], true, 3⟩, ⟨(.inl .r4c, false), [2, 3, 4, 5], true, 2⟩, ⟨(.inl .r1a, false), [3, 5], true, 3⟩, ⟨(.inl .r2d, false), [3, 5], false, 4⟩,
      ⟨(.inl .r1b, false), [3], true, 3⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 3⟩, ⟨(.inl .r2d, false), [3, 5], false, 4⟩, ⟨(.inr .k21, false), [1, 3, 4, 5], true, 4⟩,
      ⟨(.inl .r5a, false), [0, 1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 2⟩]
  | false, true, true, false =>
    [⟨(.inl .r1b, false), [1], false, 3⟩, ⟨(.inl .r1c, false), [1, 3, 4, 5], false, 4⟩, ⟨(.inl .r1a, false), [2, 3], false, 0⟩, ⟨(.inl .r1a, false), [4, 5], false, 1⟩,
      ⟨(.inl .r4a, false), [2, 3, 4, 5], true, 3⟩, ⟨(.inl .r4c, false), [2, 3, 4, 5], true, 2⟩, ⟨(.inl .r1a, false), [3, 5], true, 3⟩, ⟨(.inl .r2d, false), [3, 5], false, 4⟩,
      ⟨(.inl .r1b, false), [3], true, 3⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 3⟩, ⟨(.inl .r2d, false), [1, 5], false, 4⟩, ⟨(.inr .k32, false), [1, 3, 4, 5], true, 4⟩,
      ⟨(.inl .r5a, false), [0, 1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 2⟩]
  | true, false, false, true =>
    [⟨(.inl .r1b, false), [3], false, 3⟩, ⟨(.inl .r1c, false), [1, 3, 4, 5], false, 4⟩, ⟨(.inl .r1a, false), [2, 3], false, 0⟩, ⟨(.inl .r1a, false), [4, 5], false, 1⟩,
      ⟨(.inl .r4a, false), [2, 3, 4, 5], true, 3⟩, ⟨(.inl .r4c, false), [2, 3, 4, 5], true, 2⟩, ⟨(.inl .r1a, false), [3, 5], true, 3⟩, ⟨(.inl .r2d, false), [2, 5], false, 4⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 3⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 5⟩, ⟨(.inr .k11, false), [0, 1, 2, 3], true, 3⟩, ⟨(.inl .r2d, false), [3, 5], false, 6⟩,
      ⟨(.inl .r2a, false), [0, 2, 1, 3], true, 4⟩, ⟨(.inl .r2b, false), [0, 2, 3], true, 5⟩, ⟨(.inl .r2b, false), [0, 2, 5], true, 6⟩, ⟨(.inl .r3c, false), [1, 3], true, 4⟩,
      ⟨(.inl .r2b, false), [1, 3, 5], true, 5⟩, ⟨(.inl .r2c, false), [0, 2, 1, 3, 4, 5], true, 7⟩, ⟨(.inl .r4a, false), [1, 3, 4, 5], true, 6⟩, ⟨(.inr .k32, false), [1, 3, 4, 5], true, 4⟩,
      ⟨(.inl .r2d, false), [3, 4], true, 8⟩, ⟨(.inl .r2d, false), [3, 5], true, 9⟩, ⟨(.inl .r2d, false), [4, 5], true, 8⟩, ⟨(.inl .r3c, false), [3, 5], false, 10⟩,
      ⟨(.inl .r2b, false), [3, 5, 4], false, 9⟩, ⟨(.inl .r3c, true), [3, 5], true, 8⟩, ⟨(.inl .r2b, false), [3, 5, 1], false, 7⟩, ⟨(.inl .r3a, false), [3, 4, 5], true, 6⟩,
      ⟨(.inl .r3b, false), [3, 4, 5], true, 6⟩, ⟨(.inl .r2d, false), [3, 4], true, 9⟩, ⟨(.inl .r2d, false), [3, 5], true, 10⟩, ⟨(.inl .r1b, false), [3], true, 11⟩,
      ⟨(.inl .r1b, false), [5], true, 10⟩, ⟨(.inl .r2b, false), [0, 2, 4], false, 9⟩, ⟨(.inl .r2b, false), [0, 2, 1], false, 8⟩, ⟨(.inl .r2a, false), [0, 2, 4, 5], false, 7⟩,
      ⟨(.inl .r2a, false), [0, 2, 3, 5], false, 6⟩, ⟨(.inl .r2a, false), [0, 2, 1, 5], false, 5⟩, ⟨(.inl .r5a, false), [0, 1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 2⟩]
  | true, false, true, false =>
    [⟨(.inl .r1b, false), [1], false, 3⟩, ⟨(.inl .r1c, false), [1, 3, 4, 5], false, 4⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩, ⟨(.inl .r1a, false), [2, 3], false, 1⟩,
      ⟨(.inl .r1a, false), [4, 5], false, 2⟩, ⟨(.inl .r2c, false), [0, 1, 2, 3, 4, 5], true, 5⟩, ⟨(.inl .r4a, false), [2, 3, 4, 5], true, 4⟩, ⟨(.inl .r4c, false), [2, 3, 4, 5], true, 3⟩,
      ⟨(.inl .r1a, false), [3, 5], true, 4⟩, ⟨(.inl .r2b, false), [0, 1, 5], false, 5⟩, ⟨(.inl .r2b, false), [0, 1, 3], false, 4⟩, ⟨(.inl .r2d, false), [2, 5], false, 6⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 5⟩, ⟨(.inl .r2b, false), [0, 1, 2], true, 4⟩, ⟨(.inl .r2b, false), [0, 1, 3], true, 5⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 7⟩,
      ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inr .k11, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r1a, false), [1, 3], true, 6⟩, ⟨(.inl .r2d, false), [1, 3], true, 6⟩,
      ⟨(.inl .r2d, false), [1, 5], true, 7⟩, ⟨(.inl .r1b, false), [1], true, 8⟩, ⟨(.inl .r2b, false), [0, 2, 3], true, 5⟩, ⟨(.inl .r2b, false), [0, 2, 5], true, 6⟩,
      ⟨(.inl .r2c, false), [0, 2, 1, 3, 4, 5], true, 7⟩, ⟨(.inr .k21, false), [1, 3, 4, 5], true, 5⟩, ⟨(.inl .r2a, false), [0, 2, 4, 5], false, 7⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], false, 6⟩,
      ⟨(.inl .r5a, false), [0, 1, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 3⟩]
  | true, true, false, false =>
    [⟨(.inl .r1c, false), [1, 3, 4, 5], false, 4⟩, ⟨(.inr .k11, false), [0, 1, 2, 3], true, 1⟩, ⟨(.inl .r2a, false), [0, 2, 1, 3], true, 2⟩, ⟨(.inl .r2c, false), [0, 2, 1, 3, 4, 5], true, 3⟩,
      ⟨(.inl .r4a, false), [1, 3, 4, 5], true, 2⟩, ⟨(.inl .r2b, false), [0, 2, 5], false, 5⟩, ⟨(.inl .r2b, false), [0, 2, 3], false, 4⟩, ⟨(.inl .r2a, false), [0, 2, 3, 5], false, 3⟩,
      ⟨(.inl .r5a, false), [0, 1, 2, 3, 4, 5], true, 1⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 0⟩]
  | true, true, true, true =>
    [⟨(.inl .r1b, false), [3], false, 4⟩, ⟨(.inl .r1b, false), [1], false, 4⟩, ⟨(.inl .r2d, false), [1, 3], true, 5⟩, ⟨(.inl .r2d, false), [1, 3], true, 4⟩,
      ⟨(.inl .r1c, false), [1, 3, 4, 5], false, 6⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩, ⟨(.inl .r2c, false), [0, 1, 2, 3, 4, 5], true, 1⟩, ⟨(.inl .r2b, false), [0, 1, 2], true, 2⟩,
      ⟨(.inl .r2b, false), [0, 1, 3], true, 3⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inr .k11, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inl .r1a, false), [1, 3], true, 4⟩,
      ⟨(.inl .r1b, false), [3], true, 5⟩, ⟨(.inl .r1b, false), [1], true, 4⟩, ⟨(.inl .r2c, false), [0, 2, 1, 3, 4, 5], true, 3⟩, ⟨(.inl .r5a, false), [0, 1, 2, 3, 4, 5], true, 2⟩,
      ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 1⟩]
  | _, _, _, _ => []

theorem chk323_1323 : ∀ x y p q : Bool, xor (xor (xor x y) p) q = false →
    checkD (Gen.k 2 3 4 5 (by decide) (by decide) (by decide) :: (negw x 2 ++ negw y 3) ++ [Gen.k 0 1 2 3 (by decide) (by decide) (by decide)])
      (X323_1323 x y p q ++ Gen.k 0 1 2 4 (by decide) (by decide) (by decide) :: Y323_1323 x y p q ++
        Gen.k 1 3 4 5 (by decide) (by decide) (by decide) :: (negw p 1 ++ negw q 3)) (S323_1323 x y p q) = true := by
  decide +kernel

theorem tag323_1323 : ∀ x y p q : Bool, ∀ g ∈ X323_1323 x y p q ++ Y323_1323 x y p q, g.tag ≠ 2 := by
  decide

/-- Subcase 3.2.3 with `{a,b} = {1,3}`, `{α,β} = {2,3}` (from `0`). -/
theorem rel323_1323 {a0 a1 a2 a3 c d : Fin n} (h1 : a0 < a1) (h2 : a1 < a2) (h3 : a2 < a3) (h4 : a3 < c) (h5 : c < d) (x y p q : Bool)
    (hpar : xor (xor (xor x y) p) q = false) :
    ∃ Xw Yw : List (Gen n), (∀ g ∈ Xw ++ Yw, g.tag ≠ 2 ∧ extent g ≤ d.val) ∧
      Derivable (Table1 n)
        (FreeMonoid.ofList (Gen.k a2 a3 c d h3 h4 h5 :: (negw x a2 ++ negw y a3) ++
          [Gen.k a0 a1 a2 a3 h1 h2 h3]))
        (FreeMonoid.ofList (Xw ++ Gen.k a0 a1 a2 c h1 h2 (h3.trans h4) :: Yw ++
          Gen.k a1 a3 c d (h2.trans h3) h4 h5 :: (negw p a1 ++ negw q a3))) := by
  refine ⟨(X323_1323 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)),
    (Y323_1323 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)), ?_, ?_⟩
  · intro g hg
    rw [← List.map_append] at hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    refine ⟨by rw [tag_rename]; exact tag323_1323 x y p q g' hg', ?_⟩
    have := extent_rename_le (emb6 h1 h2 h3 h4 h5) g' 5 (extent_le_last g')
    rwa [emb6_5] at this
  · have hh := derivable_rename (emb6 h1 h2 h3 h4 h5) (checkD_sound (chk323_1323 x y p q hpar))
    rw [renW_ofList, renW_ofList] at hh
    convert hh using 2 <;>
      simp only [List.map_append, List.map_cons, List.map_nil, negw_rename, Gen.rename, emb6_0,
        emb6_1, emb6_2, emb6_3, emb6_4, emb6_5, List.cons_append, List.nil_append,
        List.append_assoc]

/-- `X` for `{a,b} = {2,3}`, `{α,β} = {0,2}`. -/
def X323_2302 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, true => [Gen.x 0 1 (by decide), Gen.x 2 3 (by decide)]
  | false, false, true, false => [Gen.x 0 3 (by decide), Gen.x 1 3 (by decide), Gen.x 2 3 (by decide)]
  | false, true, false, false => [Gen.x 0 1 (by decide), Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide)]
  | false, true, true, true => [Gen.x 0 3 (by decide), Gen.x 1 2 (by decide), Gen.x 4 5 (by decide)]
  | true, false, false, false => [Gen.x 0 1 (by decide), Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide)]
  | true, false, true, true => [Gen.x 0 3 (by decide), Gen.x 1 2 (by decide), Gen.x 4 5 (by decide)]
  | true, true, false, true => [Gen.x 0 1 (by decide), Gen.x 2 3 (by decide)]
  | true, true, true, false => [Gen.x 0 1 (by decide), Gen.x 2 3 (by decide), Gen.neg 0, Gen.neg 2]
  | _, _, _, _ => []

/-- `Y` for `{a,b} = {2,3}`, `{α,β} = {0,2}`. -/
def Y323_2302 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, true => [Gen.neg 1]
  | false, false, true, false => [Gen.x 3 5 (by decide), Gen.neg 1, Gen.neg 3, Gen.neg 5]
  | false, true, false, false => [Gen.x 2 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 1]
  | false, true, true, true => [Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 1, Gen.neg 2, Gen.neg 4]
  | true, false, false, false => [Gen.x 0 1 (by decide), Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 1, Gen.neg 2, Gen.neg 4]
  | true, false, true, true => [Gen.x 0 1 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 1]
  | true, true, false, true => [Gen.x 0 1 (by decide), Gen.x 3 5 (by decide), Gen.neg 1, Gen.neg 3, Gen.neg 5]
  | true, true, true, false => [Gen.neg 0]
  | _, _, _, _ => []

/-- The chains for `{a,b} = {2,3}`, `{α,β} = {0,2}`. -/
def S323_2302 : Bool → Bool → Bool → Bool → List (GStep ((Fam ⊕ MFam) × Bool) 6)
  | false, false, false, true =>
    [⟨(.inl .r1b, false), [3], false, 2⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], false, 3⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩, ⟨(.inl .r1a, false), [2, 3], false, 1⟩,
      ⟨(.inl .r3d, false), [0, 1, 2, 4, 5], true, 3⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 2⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], false, 3⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 3⟩,
      ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 3⟩, ⟨(.inl .r1a, false), [1, 3], true, 4⟩, ⟨(.inl .r1b, false), [3], true, 5⟩,
      ⟨(.inl .r2e, false), [1, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 2⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 3⟩]
  | false, false, true, false =>
    [⟨(.inl .r1b, false), [2], false, 2⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], false, 3⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩, ⟨(.inl .r1a, false), [0, 3], false, 1⟩,
      ⟨(.inl .r3a, false), [0, 1, 3], true, 0⟩, ⟨(.inl .r3b, false), [0, 1, 3], true, 0⟩, ⟨(.inl .r1a, false), [2, 3], false, 2⟩, ⟨(.inl .r3d, false), [0, 1, 2, 4, 5], true, 5⟩,
      ⟨(.inl .r2c, false), [0, 3, 1, 2, 4, 5], true, 4⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r3b, true), [0, 2, 3], false, 4⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], false, 5⟩,
      ⟨(.inl .r3a, true), [0, 1, 2], true, 4⟩, ⟨(.inl .r3a, true), [0, 1, 2], false, 4⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r3a, true), [0, 2, 3], false, 4⟩,
      ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r3b, false), [1, 2, 3], false, 5⟩,
      ⟨(.inl .r3a, false), [1, 2, 3], false, 5⟩, ⟨(.inl .r1a, false), [1, 3], true, 6⟩, ⟨(.inl .r3c, false), [2, 3], false, 7⟩, ⟨(.inl .r2b, false), [2, 3, 1], false, 6⟩,
      ⟨(.inl .r2d, false), [2, 3], false, 8⟩, ⟨(.inl .r1b, false), [3], true, 9⟩, ⟨(.inl .r3b, true), [1, 2, 3], true, 5⟩, ⟨(.inl .r3c, true), [1, 3], false, 6⟩,
      ⟨(.inl .r2b, false), [1, 3, 2], true, 7⟩, ⟨(.inl .r2d, false), [2, 3], false, 6⟩, ⟨(.inl .r1a, false), [1, 3], true, 8⟩, ⟨(.inl .r2d, false), [1, 3], false, 7⟩,
      ⟨(.inl .r2d, false), [1, 2], false, 6⟩, ⟨(.inl .r1b, false), [3], true, 8⟩, ⟨(.inl .r1b, false), [2], true, 7⟩, ⟨(.inl .r2e, false), [1, 2, 3, 4, 5], true, 6⟩,
      ⟨(.inl .r4a, false), [2, 3, 4, 5], true, 5⟩, ⟨(.inl .r2d, false), [1, 5], false, 8⟩, ⟨(.inl .r2d, false), [1, 3], false, 7⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 3⟩,
      ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 4⟩]
  | false, true, false, false =>
    [⟨(.inl .r1c, false), [2, 3, 4, 5], false, 3⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩, ⟨(.inl .r1a, false), [1, 2], false, 1⟩, ⟨(.inl .r1a, false), [2, 3], false, 2⟩,
      ⟨(.inl .r1a, false), [4, 5], false, 3⟩, ⟨(.inl .r3d, false), [0, 1, 2, 4, 5], true, 7⟩, ⟨(.inl .r4a, false), [1, 2, 4, 5], true, 6⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 5⟩,
      ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 4⟩, ⟨(.inl .r3b, false), [2, 3, 5], true, 5⟩, ⟨(.inl .r3b, false), [2, 3, 5], false, 5⟩, ⟨(.inl .r3a, false), [2, 3, 5], false, 5⟩,
      ⟨(.inl .r1a, false), [2, 5], true, 6⟩, ⟨(.inl .r2b, false), [0, 1, 5], false, 7⟩, ⟨(.inl .r2b, false), [0, 1, 2], false, 6⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], false, 5⟩,
      ⟨(.inl .r2d, false), [2, 5], false, 8⟩, ⟨(.inl .r1b, false), [2], true, 7⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 7⟩,
      ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r1a, false), [1, 3], true, 6⟩, ⟨(.inl .r2d, false), [1, 3], true, 6⟩,
      ⟨(.inl .r2d, false), [1, 5], true, 7⟩, ⟨(.inl .r2e, false), [1, 2, 3, 4, 5], true, 8⟩, ⟨(.inr .k21, false), [2, 3, 4, 5], true, 6⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 4⟩,
      ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 5⟩]
  | false, true, true, true =>
    [⟨(.inl .r1b, false), [3], false, 3⟩, ⟨(.inl .r1b, false), [2], false, 3⟩, ⟨(.inl .r2d, false), [2, 3], true, 4⟩, ⟨(.inl .r2d, false), [2, 3], true, 3⟩,
      ⟨(.inl .r1c, false), [2, 3, 4, 5], false, 5⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩, ⟨(.inl .r1a, false), [0, 3], false, 1⟩, ⟨(.inl .r3a, false), [0, 1, 3], true, 0⟩,
      ⟨(.inl .r3b, false), [0, 1, 3], true, 0⟩, ⟨(.inl .r1a, false), [1, 2], false, 1⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 2⟩, ⟨(.inl .r1a, false), [4, 5], false, 2⟩,
      ⟨(.inl .r3d, false), [0, 1, 2, 4, 5], true, 7⟩, ⟨(.inl .r2c, false), [0, 3, 1, 2, 4, 5], true, 6⟩, ⟨(.inl .r4a, false), [1, 2, 4, 5], true, 5⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 4⟩,
      ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 3⟩, ⟨(.inl .r3b, false), [2, 3, 5], true, 4⟩, ⟨(.inl .r3b, false), [2, 3, 5], false, 4⟩, ⟨(.inl .r3a, false), [2, 3, 5], false, 4⟩,
      ⟨(.inl .r1a, false), [2, 5], true, 5⟩, ⟨(.inl .r2b, false), [0, 3, 5], false, 6⟩, ⟨(.inl .r2b, false), [0, 3, 2], false, 5⟩, ⟨(.inl .r3b, true), [0, 2, 3], false, 4⟩,
      ⟨(.inl .r2b, false), [0, 1, 5], false, 7⟩, ⟨(.inl .r2b, false), [0, 1, 2], false, 6⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], false, 5⟩, ⟨(.inl .r3a, true), [0, 1, 2], true, 4⟩,
      ⟨(.inl .r2d, false), [2, 5], false, 8⟩, ⟨(.inl .r1b, false), [2], true, 7⟩, ⟨(.inl .r3a, true), [0, 1, 2], false, 4⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 5⟩,
      ⟨(.inl .r3a, true), [0, 2, 3], false, 4⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 7⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 5⟩,
      ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r3b, false), [1, 2, 3], false, 5⟩, ⟨(.inl .r3a, false), [1, 2, 3], false, 5⟩, ⟨(.inl .r1a, false), [1, 3], true, 6⟩,
      ⟨(.inl .r3c, false), [2, 3], false, 7⟩, ⟨(.inl .r2b, false), [2, 3, 1], false, 6⟩, ⟨(.inl .r2d, false), [2, 3], false, 8⟩, ⟨(.inl .r1b, false), [3], true, 9⟩,
      ⟨(.inl .r3b, true), [1, 2, 3], true, 5⟩, ⟨(.inl .r3c, true), [1, 3], false, 6⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 7⟩, ⟨(.inl .r2d, false), [2, 3], false, 6⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 8⟩, ⟨(.inl .r2d, false), [1, 3], false, 7⟩, ⟨(.inl .r2d, false), [1, 2], false, 6⟩, ⟨(.inl .r1b, false), [3], true, 8⟩,
      ⟨(.inl .r2d, false), [3, 5], false, 8⟩, ⟨(.inl .r2d, false), [2, 3], true, 7⟩, ⟨(.inl .r2d, false), [2, 5], true, 8⟩, ⟨(.inl .r1b, false), [2], true, 9⟩,
      ⟨(.inl .r2d, false), [1, 3], true, 6⟩, ⟨(.inl .r2d, false), [1, 5], true, 7⟩, ⟨(.inl .r3c, false), [2, 3], true, 5⟩, ⟨(.inl .r2b, false), [2, 3, 5], true, 6⟩,
      ⟨(.inl .r2e, false), [1, 2, 3, 4, 5], true, 8⟩, ⟨(.inl .r4a, false), [2, 3, 4, 5], true, 7⟩, ⟨(.inr .k32, false), [2, 3, 4, 5], true, 5⟩, ⟨(.inl .r2d, false), [3, 4], true, 9⟩,
      ⟨(.inl .r2d, false), [3, 5], true, 10⟩, ⟨(.inl .r2d, false), [4, 5], true, 9⟩, ⟨(.inl .r3c, false), [3, 5], false, 11⟩, ⟨(.inl .r2b, false), [3, 5, 4], false, 10⟩,
      ⟨(.inl .r3c, true), [3, 5], true, 9⟩, ⟨(.inl .r2b, false), [3, 5, 2], false, 8⟩, ⟨(.inl .r3a, false), [3, 4, 5], true, 7⟩, ⟨(.inl .r3b, false), [3, 4, 5], true, 7⟩,
      ⟨(.inl .r2d, false), [3, 4], true, 10⟩, ⟨(.inl .r2d, false), [3, 5], true, 11⟩, ⟨(.inl .r1b, false), [3], true, 12⟩, ⟨(.inl .r1b, false), [5], true, 11⟩,
      ⟨(.inl .r2d, false), [1, 4], false, 10⟩, ⟨(.inl .r2d, false), [1, 2], false, 9⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 4⟩]
  | true, false, false, false =>
    [⟨(.inl .r1c, false), [2, 3, 4, 5], false, 3⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩, ⟨(.inl .r1a, false), [1, 2], false, 1⟩, ⟨(.inl .r1a, false), [2, 3], false, 2⟩,
      ⟨(.inl .r1a, false), [4, 5], false, 3⟩, ⟨(.inl .r3d, false), [0, 1, 2, 4, 5], true, 7⟩, ⟨(.inl .r4a, false), [1, 2, 4, 5], true, 6⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 5⟩,
      ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 4⟩, ⟨(.inl .r3b, false), [2, 3, 5], true, 5⟩, ⟨(.inl .r3b, false), [2, 3, 5], false, 5⟩, ⟨(.inl .r3a, false), [2, 3, 5], false, 5⟩,
      ⟨(.inl .r1a, false), [2, 5], true, 6⟩, ⟨(.inl .r2b, false), [0, 1, 5], false, 7⟩, ⟨(.inl .r2b, false), [0, 1, 2], false, 6⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], false, 5⟩,
      ⟨(.inl .r2d, false), [0, 5], false, 8⟩, ⟨(.inl .r2d, false), [0, 2], false, 7⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r3c, true), [0, 1], false, 6⟩,
      ⟨(.inl .r2b, false), [0, 1, 2], true, 7⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 9⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 8⟩, ⟨(.inr .k31, false), [0, 1, 2, 3], true, 6⟩,
      ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inl .r3b, true), [0, 1, 3], false, 6⟩, ⟨(.inl .r3a, true), [1, 2, 3], true, 7⟩, ⟨(.inl .r3b, true), [1, 2, 3], false, 8⟩,
      ⟨(.inl .r1a, false), [1, 2], true, 7⟩, ⟨(.inl .r2d, false), [1, 3], true, 8⟩, ⟨(.inl .r2d, false), [1, 5], true, 9⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 6⟩,
      ⟨(.inl .r2b, false), [0, 1, 3], true, 7⟩, ⟨(.inl .r2b, false), [0, 1, 5], true, 8⟩, ⟨(.inl .r3c, false), [2, 3], true, 6⟩, ⟨(.inl .r2b, false), [2, 3, 5], true, 7⟩,
      ⟨(.inl .r2e, false), [1, 2, 3, 4, 5], true, 10⟩, ⟨(.inl .r2c, false), [0, 1, 2, 3, 4, 5], true, 9⟩, ⟨(.inl .r4a, false), [2, 3, 4, 5], true, 8⟩, ⟨(.inr .k32, false), [2, 3, 4, 5], true, 6⟩,
      ⟨(.inl .r2d, false), [3, 4], true, 10⟩, ⟨(.inl .r2d, false), [3, 5], true, 11⟩, ⟨(.inl .r2d, false), [4, 5], true, 10⟩, ⟨(.inl .r3c, false), [3, 5], false, 12⟩,
      ⟨(.inl .r2b, false), [3, 5, 4], false, 11⟩, ⟨(.inl .r3c, true), [3, 5], true, 10⟩, ⟨(.inl .r2b, false), [3, 5, 2], false, 9⟩, ⟨(.inl .r3a, false), [3, 4, 5], true, 8⟩,
      ⟨(.inl .r3b, false), [3, 4, 5], true, 8⟩, ⟨(.inl .r2d, false), [3, 4], true, 11⟩, ⟨(.inl .r2d, false), [3, 5], true, 12⟩, ⟨(.inl .r1b, false), [3], true, 13⟩,
      ⟨(.inl .r1b, false), [5], true, 12⟩, ⟨(.inl .r2b, false), [0, 1, 4], false, 11⟩, ⟨(.inl .r2b, false), [0, 1, 2], false, 10⟩, ⟨(.inl .r2a, false), [0, 1, 4, 5], false, 9⟩,
      ⟨(.inl .r2a, false), [0, 1, 3, 5], false, 8⟩, ⟨(.inl .r2a, false), [0, 1, 2, 5], false, 7⟩, ⟨(.inl .r2d, false), [1, 4], false, 12⟩, ⟨(.inl .r2d, false), [1, 2], false, 11⟩,
      ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 5⟩]
  | true, false, true, true =>
    [⟨(.inl .r1b, false), [3], false, 3⟩, ⟨(.inl .r1b, false), [2], false, 3⟩, ⟨(.inl .r2d, false), [2, 3], true, 4⟩, ⟨(.inl .r2d, false), [2, 3], true, 3⟩,
      ⟨(.inl .r1c, false), [2, 3, 4, 5], false, 5⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩, ⟨(.inl .r1a, false), [0, 3], false, 1⟩, ⟨(.inl .r3a, false), [0, 1, 3], true, 0⟩,
      ⟨(.inl .r3b, false), [0, 1, 3], true, 0⟩, ⟨(.inl .r1a, false), [1, 2], false, 1⟩, ⟨(.inl .r3a, false), [1, 2, 3], true, 2⟩, ⟨(.inl .r1a, false), [4, 5], false, 2⟩,
      ⟨(.inl .r3d, false), [0, 1, 2, 4, 5], true, 7⟩, ⟨(.inl .r2c, false), [0, 3, 1, 2, 4, 5], true, 6⟩, ⟨(.inl .r4a, false), [1, 2, 4, 5], true, 5⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 4⟩,
      ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 3⟩, ⟨(.inl .r3b, false), [2, 3, 5], true, 4⟩, ⟨(.inl .r3b, false), [2, 3, 5], false, 4⟩, ⟨(.inl .r3a, false), [2, 3, 5], false, 4⟩,
      ⟨(.inl .r1a, false), [2, 5], true, 5⟩, ⟨(.inl .r2b, false), [0, 3, 5], false, 6⟩, ⟨(.inl .r2b, false), [0, 3, 2], false, 5⟩, ⟨(.inl .r3b, true), [0, 2, 3], false, 4⟩,
      ⟨(.inl .r2b, false), [0, 1, 5], false, 7⟩, ⟨(.inl .r2b, false), [0, 1, 2], false, 6⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], false, 5⟩, ⟨(.inl .r3a, true), [0, 1, 2], true, 4⟩,
      ⟨(.inl .r2d, false), [0, 5], false, 8⟩, ⟨(.inl .r2d, false), [0, 2], false, 7⟩, ⟨(.inl .r3a, true), [0, 1, 2], false, 4⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 5⟩,
      ⟨(.inl .r3c, true), [0, 1], false, 6⟩, ⟨(.inl .r2b, false), [0, 1, 2], true, 7⟩, ⟨(.inl .r3a, true), [0, 2, 3], false, 4⟩, ⟨(.inl .r2b, false), [0, 2, 1], true, 5⟩,
      ⟨(.inl .r3c, false), [0, 2], true, 6⟩, ⟨(.inl .r2d, false), [0, 1], false, 5⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 9⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 8⟩,
      ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 5⟩, ⟨(.inr .ksym5, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r3b, false), [1, 2, 3], false, 5⟩,
      ⟨(.inl .r3a, false), [1, 2, 3], false, 5⟩, ⟨(.inl .r1a, false), [1, 3], true, 6⟩, ⟨(.inl .r2d, false), [1, 2], true, 6⟩, ⟨(.inl .r2b, false), [0, 2, 1], false, 7⟩,
      ⟨(.inl .r3c, true), [0, 2], true, 6⟩, ⟨(.inl .r3b, true), [0, 1, 2], false, 5⟩, ⟨(.inl .r3c, false), [1, 3], false, 8⟩, ⟨(.inl .r2b, false), [1, 3, 0], false, 7⟩,
      ⟨(.inl .r3a, false), [1, 2, 3], true, 6⟩, ⟨(.inl .r3b, false), [1, 2, 3], true, 6⟩, ⟨(.inl .r2d, false), [0, 3], false, 9⟩, ⟨(.inl .r1b, false), [0], true, 8⟩,
      ⟨(.inl .r2d, false), [1, 3], false, 8⟩, ⟨(.inl .r2d, false), [2, 3], false, 9⟩, ⟨(.inl .r1b, false), [3], true, 10⟩, ⟨(.inl .r2b, false), [2, 3, 1], true, 7⟩,
      ⟨(.inl .r3c, true), [2, 3], false, 8⟩, ⟨(.inl .r1a, false), [2, 3], true, 9⟩, ⟨(.inl .r2d, false), [2, 3], false, 8⟩, ⟨(.inl .r1b, false), [3], true, 9⟩,
      ⟨(.inl .r3c, true), [1, 3], false, 6⟩, ⟨(.inl .r2b, false), [1, 3, 2], true, 7⟩, ⟨(.inl .r2d, false), [2, 3], false, 6⟩, ⟨(.inl .r1a, false), [1, 3], true, 8⟩,
      ⟨(.inl .r2d, false), [1, 3], false, 7⟩, ⟨(.inl .r2d, false), [1, 2], false, 6⟩, ⟨(.inl .r1b, false), [3], true, 8⟩, ⟨(.inl .r2d, false), [3, 5], false, 8⟩,
      ⟨(.inl .r2d, false), [2, 3], true, 7⟩, ⟨(.inl .r2d, false), [2, 5], true, 8⟩, ⟨(.inl .r1b, false), [2], true, 9⟩, ⟨(.inl .r2d, false), [1, 3], true, 6⟩,
      ⟨(.inl .r2d, false), [1, 5], true, 7⟩, ⟨(.inl .r2b, false), [0, 1, 3], true, 5⟩, ⟨(.inl .r2b, false), [0, 1, 5], true, 6⟩, ⟨(.inl .r2e, false), [1, 2, 3, 4, 5], true, 8⟩,
      ⟨(.inl .r2c, false), [0, 1, 2, 3, 4, 5], true, 7⟩, ⟨(.inr .k21, false), [2, 3, 4, 5], true, 5⟩, ⟨(.inl .r2a, false), [0, 1, 4, 5], false, 7⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], false, 6⟩,
      ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 4⟩]
  | true, true, false, true =>
    [⟨(.inl .r1b, false), [3], false, 4⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], false, 5⟩, ⟨(.inl .r1a, false), [0, 1], false, 0⟩, ⟨(.inl .r1a, false), [2, 3], false, 1⟩,
      ⟨(.inl .r3d, false), [0, 1, 2, 4, 5], true, 3⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 2⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], false, 3⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 3⟩,
      ⟨(.inl .r3c, true), [0, 1], false, 4⟩, ⟨(.inl .r2b, false), [0, 1, 2], true, 5⟩, ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inr .k31, false), [0, 1, 2, 3], true, 4⟩,
      ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 3⟩, ⟨(.inl .r3b, true), [0, 1, 3], false, 4⟩, ⟨(.inl .r3a, true), [1, 2, 3], true, 5⟩, ⟨(.inl .r3b, true), [1, 2, 3], false, 6⟩,
      ⟨(.inl .r1a, false), [1, 2], true, 5⟩, ⟨(.inl .r1b, false), [3], true, 7⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r2e, false), [1, 2, 3, 4, 5], true, 6⟩,
      ⟨(.inl .r2c, false), [0, 1, 2, 3, 4, 5], true, 5⟩, ⟨(.inl .r4a, false), [2, 3, 4, 5], true, 4⟩, ⟨(.inl .r2b, false), [0, 1, 5], false, 7⟩, ⟨(.inl .r2b, false), [0, 1, 3], false, 6⟩,
      ⟨(.inl .r2a, false), [0, 1, 3, 5], false, 5⟩, ⟨(.inl .r2d, false), [1, 5], false, 8⟩, ⟨(.inl .r2d, false), [1, 3], false, 7⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 2⟩,
      ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 3⟩]
  | true, true, true, false =>
    [⟨(.inl .r1b, false), [2], false, 4⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], false, 5⟩, ⟨(.inl .r1b, false), [1], false, 0⟩, ⟨(.inl .r1b, false), [3], false, 1⟩,
      ⟨(.inl .r1a, false), [0, 1], false, 2⟩, ⟨(.inl .r2b, false), [0, 1, 3], false, 1⟩, ⟨(.inl .r3c, true), [0, 1], true, 0⟩, ⟨(.inl .r1a, false), [2, 3], false, 3⟩,
      ⟨(.inl .r3c, true), [2, 3], true, 2⟩, ⟨(.inl .r2b, false), [2, 3, 0], false, 1⟩, ⟨(.inl .r2e, false), [1, 0, 2, 4, 5], true, 7⟩, ⟨(.inl .r2e, false), [3, 0, 2, 4, 5], true, 6⟩,
      ⟨(.inl .r3d, false), [0, 1, 2, 4, 5], true, 5⟩, ⟨(.inl .r3e, false), [1, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], false, 5⟩, ⟨(.inl .r2d, false), [1, 3], false, 7⟩,
      ⟨(.inl .r2d, false), [0, 3], false, 8⟩, ⟨(.inl .r2d, false), [0, 1], false, 7⟩, ⟨(.inl .r2d, false), [2, 3], false, 9⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 5⟩,
      ⟨(.inl .r3c, true), [0, 1], false, 6⟩, ⟨(.inl .r3c, false), [0, 1], true, 7⟩, ⟨(.inl .r2b, false), [0, 1, 2], true, 8⟩, ⟨(.inl .r2b, false), [0, 1, 3], true, 9⟩,
      ⟨(.inl .r2d, false), [0, 1], false, 6⟩, ⟨(.inl .r2d, false), [1, 2], true, 7⟩, ⟨(.inl .r2d, false), [1, 3], true, 8⟩, ⟨(.inl .r2d, false), [0, 2], true, 6⟩,
      ⟨(.inl .r2d, false), [0, 3], true, 7⟩, ⟨(.inl .r3c, true), [2, 3], false, 5⟩, ⟨(.inl .r3c, false), [2, 3], true, 6⟩, ⟨(.inl .r2d, false), [2, 3], false, 5⟩,
      ⟨(.inl .r4a, false), [0, 1, 2, 3], true, 10⟩, ⟨(.inr .k12, false), [0, 1, 2, 3], true, 8⟩, ⟨(.inl .r4c, false), [0, 1, 2, 3], true, 7⟩, ⟨(.inr .k11, false), [0, 1, 2, 3], true, 5⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 7⟩, ⟨(.inl .r1a, false), [0, 2], true, 6⟩, ⟨(.inl .r2b, false), [1, 3, 0], true, 6⟩, ⟨(.inl .r3c, true), [1, 3], false, 7⟩,
      ⟨(.inl .r2b, false), [1, 3, 2], true, 8⟩, ⟨(.inl .r2d, false), [2, 3], false, 7⟩, ⟨(.inl .r3c, false), [1, 3], true, 9⟩, ⟨(.inl .r2d, false), [1, 3], false, 8⟩,
      ⟨(.inl .r1a, false), [1, 3], true, 10⟩, ⟨(.inl .r2d, false), [1, 2], false, 7⟩, ⟨(.inl .r2d, false), [1, 2], true, 7⟩, ⟨(.inl .r2d, false), [1, 3], true, 8⟩,
      ⟨(.inl .r1b, false), [1], true, 9⟩, ⟨(.inl .r1b, false), [3], true, 8⟩, ⟨(.inl .r1b, false), [2], true, 7⟩, ⟨(.inl .r2e, false), [0, 2, 3, 4, 5], true, 6⟩,
      ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 4⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 5⟩]
  | _, _, _, _ => []

theorem chk323_2302 : ∀ x y p q : Bool, xor (xor (xor x y) p) q = true →
    checkD (Gen.k 0 2 4 5 (by decide) (by decide) (by decide) :: (negw x 0 ++ negw y 2) ++ [Gen.k 0 1 2 3 (by decide) (by decide) (by decide)])
      (X323_2302 x y p q ++ Gen.k 0 1 2 4 (by decide) (by decide) (by decide) :: Y323_2302 x y p q ++
        Gen.k 2 3 4 5 (by decide) (by decide) (by decide) :: (negw p 2 ++ negw q 3)) (S323_2302 x y p q) = true := by
  decide +kernel

theorem tag323_2302 : ∀ x y p q : Bool, ∀ g ∈ X323_2302 x y p q ++ Y323_2302 x y p q, g.tag ≠ 2 := by
  decide

/-- Subcase 3.2.3 with `{a,b} = {2,3}`, `{α,β} = {0,2}` (from `0`). -/
theorem rel323_2302 {a0 a1 a2 a3 c d : Fin n} (h1 : a0 < a1) (h2 : a1 < a2) (h3 : a2 < a3) (h4 : a3 < c) (h5 : c < d) (x y p q : Bool)
    (hpar : xor (xor (xor x y) p) q = true) :
    ∃ Xw Yw : List (Gen n), (∀ g ∈ Xw ++ Yw, g.tag ≠ 2 ∧ extent g ≤ d.val) ∧
      Derivable (Table1 n)
        (FreeMonoid.ofList (Gen.k a0 a2 c d (h1.trans h2) (h3.trans h4) h5 :: (negw x a0 ++ negw y a2) ++
          [Gen.k a0 a1 a2 a3 h1 h2 h3]))
        (FreeMonoid.ofList (Xw ++ Gen.k a0 a1 a2 c h1 h2 (h3.trans h4) :: Yw ++
          Gen.k a2 a3 c d h3 h4 h5 :: (negw p a2 ++ negw q a3))) := by
  refine ⟨(X323_2302 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)),
    (Y323_2302 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)), ?_, ?_⟩
  · intro g hg
    rw [← List.map_append] at hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    refine ⟨by rw [tag_rename]; exact tag323_2302 x y p q g' hg', ?_⟩
    have := extent_rename_le (emb6 h1 h2 h3 h4 h5) g' 5 (extent_le_last g')
    rwa [emb6_5] at this
  · have hh := derivable_rename (emb6 h1 h2 h3 h4 h5) (checkD_sound (chk323_2302 x y p q hpar))
    rw [renW_ofList, renW_ofList] at hh
    convert hh using 2 <;>
      simp only [List.map_append, List.map_cons, List.map_nil, negw_rename, Gen.rename, emb6_0,
        emb6_1, emb6_2, emb6_3, emb6_4, emb6_5, List.cons_append, List.nil_append,
        List.append_assoc]

/-- `X` for `{a,b} = {2,3}`, `{α,β} = {1,3}`. -/
def X323_2313 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, false => []
  | false, false, true, true => [Gen.x 0 2 (by decide)]
  | false, true, false, true => [Gen.x 1 3 (by decide), Gen.x 4 5 (by decide)]
  | false, true, true, false => [Gen.x 1 3 (by decide), Gen.x 4 5 (by decide)]
  | true, false, false, true => [Gen.x 1 3 (by decide), Gen.x 4 5 (by decide)]
  | true, false, true, false => [Gen.x 0 2 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide)]
  | true, true, false, false => []
  | true, true, true, true => [Gen.x 0 2 (by decide)]
  | _, _, _, _ => []

/-- `Y` for `{a,b} = {2,3}`, `{α,β} = {1,3}`. -/
def Y323_2313 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, false => []
  | false, false, true, true => [Gen.x 3 5 (by decide), Gen.neg 3, Gen.neg 5]
  | false, true, false, true => [Gen.x 2 3 (by decide), Gen.x 4 5 (by decide)]
  | false, true, true, false => [Gen.x 2 5 (by decide), Gen.x 3 4 (by decide), Gen.neg 2, Gen.neg 3, Gen.neg 4, Gen.neg 5]
  | true, false, false, true => [Gen.x 0 1 (by decide), Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 2, Gen.neg 4]
  | true, false, true, false => [Gen.x 0 1 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide)]
  | true, true, false, false => [Gen.x 0 1 (by decide), Gen.x 3 5 (by decide), Gen.neg 3, Gen.neg 5]
  | true, true, true, true => [Gen.x 0 1 (by decide)]
  | _, _, _, _ => []

/-- The chains for `{a,b} = {2,3}`, `{α,β} = {1,3}`. -/
def S323_2313 : Bool → Bool → Bool → Bool → List (GStep ((Fam ⊕ MFam) × Bool) 6)
  | false, false, false, false =>
    [⟨(.inl .r1c, false), [2, 3, 4, 5], false, 2⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 0⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 1⟩]
  | false, false, true, true =>
    [⟨(.inl .r1b, false), [3], false, 2⟩, ⟨(.inl .r1b, false), [2], false, 2⟩, ⟨(.inl .r2d, false), [2, 3], true, 3⟩, ⟨(.inl .r2d, false), [2, 3], true, 2⟩,
      ⟨(.inl .r1c, false), [2, 3, 4, 5], false, 4⟩, ⟨(.inl .r1a, false), [0, 2], false, 0⟩, ⟨(.inl .r2c, false), [0, 2, 1, 3, 4, 5], true, 1⟩, ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 2⟩,
      ⟨(.inl .r1b, false), [3], true, 5⟩, ⟨(.inl .r1b, false), [2], true, 4⟩, ⟨(.inl .r4a, false), [2, 3, 4, 5], true, 3⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 1⟩,
      ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 2⟩]
  | false, true, false, true =>
    [⟨(.inl .r1b, false), [3], false, 3⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], false, 4⟩, ⟨(.inl .r1a, false), [1, 3], false, 0⟩, ⟨(.inl .r1a, false), [4, 5], false, 1⟩,
      ⟨(.inl .r4a, false), [1, 3, 4, 5], true, 3⟩, ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 2⟩, ⟨(.inl .r1a, false), [3, 5], true, 3⟩, ⟨(.inl .r2d, false), [3, 5], false, 4⟩,
      ⟨(.inl .r1b, false), [3], true, 3⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 3⟩, ⟨(.inl .r2d, false), [3, 5], false, 4⟩, ⟨(.inr .k21, false), [2, 3, 4, 5], true, 4⟩,
      ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 2⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 3⟩]
  | false, true, true, false =>
    [⟨(.inl .r1b, false), [2], false, 3⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], false, 4⟩, ⟨(.inl .r1a, false), [1, 3], false, 0⟩, ⟨(.inl .r1a, false), [4, 5], false, 1⟩,
      ⟨(.inl .r4a, false), [1, 3, 4, 5], true, 3⟩, ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 2⟩, ⟨(.inl .r1a, false), [3, 5], true, 3⟩, ⟨(.inl .r2d, false), [3, 5], false, 4⟩,
      ⟨(.inl .r1b, false), [3], true, 3⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 3⟩, ⟨(.inl .r2d, false), [2, 5], false, 4⟩, ⟨(.inr .k32, false), [2, 3, 4, 5], true, 4⟩,
      ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 2⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 3⟩]
  | true, false, false, true =>
    [⟨(.inl .r1b, false), [3], false, 3⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], false, 4⟩, ⟨(.inl .r1a, false), [1, 3], false, 0⟩, ⟨(.inl .r1a, false), [4, 5], false, 1⟩,
      ⟨(.inl .r4a, false), [1, 3, 4, 5], true, 3⟩, ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 2⟩, ⟨(.inl .r1a, false), [3, 5], true, 3⟩, ⟨(.inl .r2d, false), [1, 5], false, 4⟩,
      ⟨(.inl .r2d, false), [1, 3], false, 3⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 5⟩, ⟨(.inr .k21, false), [0, 1, 2, 3], true, 3⟩, ⟨(.inl .r2d, false), [3, 5], false, 6⟩,
      ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r2b, false), [0, 1, 3], true, 5⟩, ⟨(.inl .r2b, false), [0, 1, 5], true, 6⟩, ⟨(.inl .r3c, false), [2, 3], true, 4⟩,
      ⟨(.inl .r2b, false), [2, 3, 5], true, 5⟩, ⟨(.inl .r2c, false), [0, 1, 2, 3, 4, 5], true, 7⟩, ⟨(.inl .r4a, false), [2, 3, 4, 5], true, 6⟩, ⟨(.inr .k32, false), [2, 3, 4, 5], true, 4⟩,
      ⟨(.inl .r2d, false), [3, 4], true, 8⟩, ⟨(.inl .r2d, false), [3, 5], true, 9⟩, ⟨(.inl .r2d, false), [4, 5], true, 8⟩, ⟨(.inl .r3c, false), [3, 5], false, 10⟩,
      ⟨(.inl .r2b, false), [3, 5, 4], false, 9⟩, ⟨(.inl .r3c, true), [3, 5], true, 8⟩, ⟨(.inl .r2b, false), [3, 5, 2], false, 7⟩, ⟨(.inl .r3a, false), [3, 4, 5], true, 6⟩,
      ⟨(.inl .r3b, false), [3, 4, 5], true, 6⟩, ⟨(.inl .r2d, false), [3, 4], true, 9⟩, ⟨(.inl .r2d, false), [3, 5], true, 10⟩, ⟨(.inl .r1b, false), [3], true, 11⟩,
      ⟨(.inl .r1b, false), [5], true, 10⟩, ⟨(.inl .r2b, false), [0, 1, 4], false, 9⟩, ⟨(.inl .r2b, false), [0, 1, 2], false, 8⟩, ⟨(.inl .r2a, false), [0, 1, 4, 5], false, 7⟩,
      ⟨(.inl .r2a, false), [0, 1, 3, 5], false, 6⟩, ⟨(.inl .r2a, false), [0, 1, 2, 5], false, 5⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 2⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 3⟩]
  | true, false, true, false =>
    [⟨(.inl .r1b, false), [2], false, 3⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], false, 4⟩, ⟨(.inl .r1a, false), [0, 2], false, 0⟩, ⟨(.inl .r1a, false), [1, 3], false, 1⟩,
      ⟨(.inl .r1a, false), [4, 5], false, 2⟩, ⟨(.inl .r2c, false), [0, 2, 1, 3, 4, 5], true, 5⟩, ⟨(.inl .r4a, false), [1, 3, 4, 5], true, 4⟩, ⟨(.inl .r4c, false), [1, 3, 4, 5], true, 3⟩,
      ⟨(.inl .r1a, false), [3, 5], true, 4⟩, ⟨(.inl .r2b, false), [0, 2, 5], false, 5⟩, ⟨(.inl .r2b, false), [0, 2, 3], false, 4⟩, ⟨(.inl .r2d, false), [1, 5], false, 6⟩,
      ⟨(.inl .r2d, false), [1, 3], false, 5⟩, ⟨(.inl .r2b, false), [0, 2, 1], true, 4⟩, ⟨(.inl .r2b, false), [0, 2, 3], true, 5⟩, ⟨(.inl .r2e, false), [5, 0, 1, 2, 3], true, 7⟩,
      ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 6⟩, ⟨(.inr .k21, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inl .r1a, false), [2, 3], true, 6⟩, ⟨(.inl .r2d, false), [2, 3], true, 6⟩,
      ⟨(.inl .r2d, false), [2, 5], true, 7⟩, ⟨(.inl .r1b, false), [2], true, 8⟩, ⟨(.inl .r2b, false), [0, 1, 3], true, 5⟩, ⟨(.inl .r2b, false), [0, 1, 5], true, 6⟩,
      ⟨(.inl .r2c, false), [0, 1, 2, 3, 4, 5], true, 7⟩, ⟨(.inr .k21, false), [2, 3, 4, 5], true, 5⟩, ⟨(.inl .r2a, false), [0, 1, 4, 5], false, 7⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], false, 6⟩,
      ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 4⟩]
  | true, true, false, false =>
    [⟨(.inl .r1c, false), [2, 3, 4, 5], false, 4⟩, ⟨(.inr .k21, false), [0, 1, 2, 3], true, 1⟩, ⟨(.inl .r2a, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inl .r2c, false), [0, 1, 2, 3, 4, 5], true, 3⟩,
      ⟨(.inl .r4a, false), [2, 3, 4, 5], true, 2⟩, ⟨(.inl .r2b, false), [0, 1, 5], false, 5⟩, ⟨(.inl .r2b, false), [0, 1, 3], false, 4⟩, ⟨(.inl .r2a, false), [0, 1, 3, 5], false, 3⟩,
      ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 0⟩, ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 1⟩]
  | true, true, true, true =>
    [⟨(.inl .r1b, false), [3], false, 4⟩, ⟨(.inl .r1b, false), [2], false, 4⟩, ⟨(.inl .r2d, false), [2, 3], true, 5⟩, ⟨(.inl .r2d, false), [2, 3], true, 4⟩,
      ⟨(.inl .r1c, false), [2, 3, 4, 5], false, 6⟩, ⟨(.inl .r1a, false), [0, 2], false, 0⟩, ⟨(.inl .r2c, false), [0, 2, 1, 3, 4, 5], true, 1⟩, ⟨(.inl .r2b, false), [0, 2, 1], true, 2⟩,
      ⟨(.inl .r2b, false), [0, 2, 3], true, 3⟩, ⟨(.inr .ksym4, false), [0, 1, 2, 3], true, 4⟩, ⟨(.inr .k21, false), [0, 1, 2, 3], true, 2⟩, ⟨(.inl .r1a, false), [2, 3], true, 4⟩,
      ⟨(.inl .r1b, false), [3], true, 5⟩, ⟨(.inl .r1b, false), [2], true, 4⟩, ⟨(.inl .r2c, false), [0, 1, 2, 3, 4, 5], true, 3⟩, ⟨(.inl .r5a, true), [0, 1, 2, 3, 4, 5], true, 1⟩,
      ⟨(.inl .r1c, false), [2, 3, 4, 5], true, 2⟩]
  | _, _, _, _ => []

theorem chk323_2313 : ∀ x y p q : Bool, xor (xor (xor x y) p) q = false →
    checkD (Gen.k 1 3 4 5 (by decide) (by decide) (by decide) :: (negw x 1 ++ negw y 3) ++ [Gen.k 0 1 2 3 (by decide) (by decide) (by decide)])
      (X323_2313 x y p q ++ Gen.k 0 1 2 4 (by decide) (by decide) (by decide) :: Y323_2313 x y p q ++
        Gen.k 2 3 4 5 (by decide) (by decide) (by decide) :: (negw p 2 ++ negw q 3)) (S323_2313 x y p q) = true := by
  decide +kernel

theorem tag323_2313 : ∀ x y p q : Bool, ∀ g ∈ X323_2313 x y p q ++ Y323_2313 x y p q, g.tag ≠ 2 := by
  decide

/-- Subcase 3.2.3 with `{a,b} = {2,3}`, `{α,β} = {1,3}` (from `0`). -/
theorem rel323_2313 {a0 a1 a2 a3 c d : Fin n} (h1 : a0 < a1) (h2 : a1 < a2) (h3 : a2 < a3) (h4 : a3 < c) (h5 : c < d) (x y p q : Bool)
    (hpar : xor (xor (xor x y) p) q = false) :
    ∃ Xw Yw : List (Gen n), (∀ g ∈ Xw ++ Yw, g.tag ≠ 2 ∧ extent g ≤ d.val) ∧
      Derivable (Table1 n)
        (FreeMonoid.ofList (Gen.k a1 a3 c d (h2.trans h3) h4 h5 :: (negw x a1 ++ negw y a3) ++
          [Gen.k a0 a1 a2 a3 h1 h2 h3]))
        (FreeMonoid.ofList (Xw ++ Gen.k a0 a1 a2 c h1 h2 (h3.trans h4) :: Yw ++
          Gen.k a2 a3 c d h3 h4 h5 :: (negw p a2 ++ negw q a3))) := by
  refine ⟨(X323_2313 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)),
    (Y323_2313 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)), ?_, ?_⟩
  · intro g hg
    rw [← List.map_append] at hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    refine ⟨by rw [tag_rename]; exact tag323_2313 x y p q g' hg', ?_⟩
    have := extent_rename_le (emb6 h1 h2 h3 h4 h5) g' 5 (extent_le_last g')
    rwa [emb6_5] at this
  · have hh := derivable_rename (emb6 h1 h2 h3 h4 h5) (checkD_sound (chk323_2313 x y p q hpar))
    rw [renW_ofList, renW_ofList] at hh
    convert hh using 2 <;>
      simp only [List.map_append, List.map_cons, List.map_nil, negw_rename, Gen.rename, emb6_0,
        emb6_1, emb6_2, emb6_3, emb6_4, emb6_5, List.cons_append, List.nil_append,
        List.append_assoc]

end QCert.LiRossSelinger
