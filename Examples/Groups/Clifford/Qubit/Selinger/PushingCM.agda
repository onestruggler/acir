------------------------------------------------------------------------
-- Presentations of groups
--
-- Normalization (arXiv:1310.6813, §6): the C box, and dirt crossing
-- into the staircase.
--
-- A Z-normal circuit ends with its C box, on the un-shifted wire, and
-- the X-normal staircase begins immediately to its right.  So the C box
-- is the join, and everything the chain sends rightwards passes through
-- it before reaching M(n).
--
-- Which is a narrowing.  The C rules are commXC, commSC and commZZCI,
-- and between them they emit only S gates and controlled-Zs -- an X
-- meeting a C box is absorbed by it (X·C₁ = C₂, X·C₂ = C₁), and nothing
-- emits an H on the un-shifted wire.  So of the ten dirty gates only
-- four can enter a staircase, which is what AtM records:
--
--   S on the un-shifted wire      ascends to the E box (altSIDD)
--   S on the wire above           meets the bottom box (altISDD)
--   H on the wire above           meets the bottom box (altIHDD)
--   a controlled-Z on the pair    meets the bottom box (altZZDD)
--
-- and an H or an X on the un-shifted wire cannot, which is exactly why
-- the paper has no rule for either.  That was a remark in PushingM; here
-- it is a type.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Clifford.Qubit.Selinger.PushingCM
  (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.List using (List ; [] ; _∷_ ; _++_)
open import Data.Product using (_×_ ; _,_)

open import ForStdlib.Data.Fin.Mod using (ℤ ; _+_ ; ₀ ; ₂)
open import Notations using (₁₊)

open import Examples.Groups.Clifford.Qubit.Selinger.Boxes p-2 p-prime
open import Examples.Groups.Clifford.Qubit.Selinger.Normal p-2 p-prime
  using (Mx)
open import Examples.Groups.Clifford.Qubit.Selinger.Pushing p-2 p-prime
  using (Dirty)
open import Examples.Groups.Clifford.Qubit.Selinger.PushingM p-2 p-prime
  using (pushS-Mx ; pushS₁-Mx ; pushH₁-Mx ; pushZZ-Mx)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- What can enter a staircase

data AtM : Set where
  mS₀ mS₁ mH₁ mZZ : AtM

-- One gate into the staircase.  Only mS₀ is special: it ascends the
-- whole staircase to the E box without touching a D, so it escapes
-- nothing and costs no phase.
push1-Mx : AtM → Mx (₁₊ n) → ℤ 8 × List Dirty × Mx (₁₊ n)
push1-Mx mS₀ m = ₀ , [] , pushS-Mx 1 m
push1-Mx mS₁ m = pushS₁-Mx m
push1-Mx mH₁ m = pushH₁-Mx m
push1-Mx mZZ m = pushZZ-Mx m

-- A word of them.  As everywhere in §6, the gate nearest the staircase
-- is the last of the list, so the list is consumed from the right; the
-- dirt that escapes keeps that order, the leftmost gate's escape coming
-- first.
push-Mx : List AtM → Mx (₁₊ n) → ℤ 8 × List Dirty × Mx (₁₊ n)
push-Mx []       m = ₀ , [] , m
push-Mx (a ∷ as) m with push-Mx as m
... | k₂ , o₂ , m′ with push1-Mx a m′
...   | k₁ , o₁ , m″ = k₁ + k₂ , o₁ ++ o₂ , m″

------------------------------------------------------------------------
-- What can arrive at the C box
--
-- An X, an S, or a controlled-Z on the pair above it.  An H cannot: the
-- chain's B rules emit H gates only on their upper wire, and the C box
-- sits below all of them.

data AtC : Set where
  cX cS cZZ : AtC

------------------------------------------------------------------------
-- Crossing the join
--
-- Rewrite the C box, then send what it emits into the staircase.  The
-- three families:
--
--   commXC    X·C₁ = C₂, X·C₂ = C₁.  The box absorbs it; nothing
--             reaches the staircase at all.
--   commSC    S·C₁ = C₁·S and S·C₂ = ω²·C₂·S³.  The S gates land on the
--             un-shifted wire, so they ascend to E and vanish; only the
--             phase of the second clause survives.
--   commZZCI  ZZ·C₁ = C₁·ZZ and ZZ·C₂ = C₂·ZZ·S₁².  Here the emitted
--             word matters: the S gates sit to the RIGHT of the
--             controlled-Z, so they meet the staircase first.

pushC-Mx : AtC → CBox → Mx (₁₊ n) → ℤ 8 × List Dirty × CBox × Mx (₁₊ n)
pushC-Mx cX c₁ m = ₀ , [] , c₂ , m
pushC-Mx cX c₂ m = ₀ , [] , c₁ , m
pushC-Mx cS c₁ m with push-Mx (mS₀ ∷ []) m
... | k , o , m′ = k , o , c₁ , m′
pushC-Mx cS c₂ m with push-Mx (mS₀ ∷ mS₀ ∷ mS₀ ∷ []) m
... | k , o , m′ = ₂ + k , o , c₂ , m′
pushC-Mx cZZ c₁ m with push-Mx (mZZ ∷ []) m
... | k , o , m′ = k , o , c₁ , m′
pushC-Mx cZZ c₂ m with push-Mx (mZZ ∷ mS₁ ∷ mS₁ ∷ []) m
... | k , o , m′ = k , o , c₂ , m′
