------------------------------------------------------------------------
-- Presentations of groups
--
-- Bitstring utilities for the encoding and decoding of Section 8:
-- enumeration, insertion and removal at a wire, the wires where two
-- strings differ
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings where

open import Data.Bool using (Bool ; true ; false ; _xor_ ; if_then_else_)
open import Data.List using (List ; [] ; _∷_ ; _++_ ; map)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _∸_ ; _<ᵇ_ ; _≡ᵇ_)
open import Data.Vec using (Vec ; [] ; _∷_)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)

private
  variable
    n : ℕ

-- Every bitstring of a length, in increasing binary order (wire 0 is
-- the least significant bit).
allBits : (n : ℕ) → List (Bits n)
allBits zero    = [] ∷ []
allBits (suc n) = map (false ∷_) (allBits n) ++ map (true ∷_) (allBits n)

-- The bit at wire i (false beyond the top wire).
lookupℕ : ℕ → Bits n → Bool
lookupℕ _       []       = false
lookupℕ zero    (b ∷ _)  = b
lookupℕ (suc i) (_ ∷ bs) = lookupℕ i bs

-- Insertion of a bit at wire i (at the top if i is beyond it).
insertℕ : ℕ → Bool → Bits n → Bits (suc n)
insertℕ zero    b bs       = b ∷ bs
insertℕ (suc i) b []       = b ∷ []
insertℕ (suc i) b (c ∷ bs) = c ∷ insertℕ i b bs

-- Removal of the bit at wire i (of the top wire if i is beyond it).
removeℕ : ℕ → Bits (suc n) → Bits n
removeℕ zero    (_ ∷ bs)     = bs
removeℕ (suc i) (b ∷ [])     = []
removeℕ (suc i) (b ∷ c ∷ bs) = b ∷ removeℕ i (c ∷ bs)

-- The wires at which two strings differ, from wire 0 up.
diff : Bits n → Bits n → List ℕ
diff xs ys = go 0 xs ys
  where
  go : ℕ → Bits n → Bits n → List ℕ
  go i []       []       = []
  go i (x ∷ xs) (y ∷ ys) = if x xor y then i ∷ go (suc i) xs ys else go (suc i) xs ys

-- Bitwise exclusive or.
xorB : Bits n → Bits n → Bits n
xorB []       []       = []
xorB (x ∷ xs) (y ∷ ys) = (x xor y) ∷ xorB xs ys

-- Flipping the bit at wire i.
flipℕ : ℕ → Bits n → Bits n
flipℕ _       []       = []
flipℕ zero    (b ∷ bs) = (true xor b) ∷ bs
flipℕ (suc i) (b ∷ bs) = b ∷ flipℕ i bs

-- The string that is b at wire i and false elsewhere: a unit vector.
unit : (n : ℕ) → ℕ → Bits n
unit zero    _       = []
unit (suc n) zero    = true ∷ unit n zero
unit (suc n) (suc i) = false ∷ unit n i
