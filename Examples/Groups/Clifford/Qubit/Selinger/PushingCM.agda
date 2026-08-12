------------------------------------------------------------------------
-- Presentations of groups
--
-- Normalization (arXiv:1310.6813, §6): the C box, and dirt crossing
-- into the staircase.
--
-- A Z-normal circuit ends with its C box, on the un-shifted wire, and
-- the X-normal staircase begins immediately to its right.
--
-- The C rules are commXC, commSC and commZZCI, and between them they
-- emit only S gates and controlled-Zs -- an X meeting a C box is
-- absorbed by it (X·C₁ = C₂, X·C₂ = C₁), and nothing emits an H on the
-- un-shifted wire.  So what the C BOX sends into a staircase is just
-- four things, which is what AtM records:
--
--   S on the un-shifted wire      ascends to the E box (altSIDD)
--   S on the wire above           meets the bottom box (altISDD)
--   H on the wire above           meets the bottom box (altIHDD)
--   a controlled-Z on the pair    meets the bottom box (altZZDD)
--
-- An H or an X on the un-shifted wire is not among them, which is why
-- the paper has no rule for either meeting a D box at its qubit 0.
--
-- WHAT THIS DOES NOT COVER.  Not everything reaching M(n) comes through
-- the C box.  Dirt on wires above the un-shifted one COMMUTES PAST the C
-- box rather than meeting it, and so arrives at the staircase directly:
-- commZZIIBBBBI, for one, leaves H gates on wire 2 and a controlled-Z on
-- (1,2) to the right of the whole chain, and those meet M(n) at their own
-- level rather than at its bottom.  An earlier draft of this banner
-- claimed the C box was the only way in and that AtM was therefore
-- exhaustive; it is not, and the four constructors are only the C box's
-- own output.
--
-- Closing that needs the staircase traversal to be indexed by the wire
-- the dirt arrives on, since a controlled-Z can enter the chain at any
-- adjacent pair and its rewrite emits dirt two wires up from there.  The
-- functions below are the level-0 case, which is what the C box needs
-- and no more.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Clifford.Qubit.Selinger.PushingCM
  (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.List using (List ; [] ; _∷_ ; _++_ ; map)
open import Data.Product using (_×_ ; _,_)

open import ForStdlib.Data.Fin.Mod using (ℤ ; _+_ ; ₀ ; ₂)
open import Notations using (₁₊)

open import Examples.Groups.Clifford.Qubit.Selinger.Boxes p-2 p-prime
open import Examples.Groups.Clifford.Qubit.Selinger.Normal p-2 p-prime
  using (Mx)
open import Examples.Groups.Clifford.Qubit.Selinger.Placed p-2 p-prime
  using (Placed ; _at_ ; kH ; kS ; kX ; kZZ ; places)
open import Examples.Groups.Clifford.Qubit.Selinger.Pushing p-2 p-prime
  using (Dirty ; S₀ ; pushZZC)
open import Examples.Groups.Clifford.Qubit.Selinger.Rewrite p-2 p-prime
  using (DirtE ; dX ; dS ; pushC)
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

------------------------------------------------------------------------
-- A placed gate meeting the C box
--
-- The C box sits on the un-shifted wire, so only a gate there meets it;
-- anything higher commutes past on its way to the staircase.  The rules
-- are commXC, commSC and commZZCI, and a controlled-Z counts because on
-- (0,1) its lower wire is the C box's.
--
-- There is no rule for an H meeting a C box, and nothing delivers one:
-- at the un-shifted wire the chain emits only X (commHIB, commSIB,
-- commIXB) and S (commISB, and the A rules), never an H.  So that
-- clause is a precondition, like the controlled-Z one in Placed.

-- What a C box emits is narrower still than what it takes: DirtE has
-- only the S gate, since commXC emits nothing and commSC only S.
fromDirtE : DirtE → Dirty
fromDirtE dS = S₀

pushC1 : Placed → CBox → ℤ 8 × CBox × List Placed
pushC1 (kX at 0)      c with pushC dX c
... | k , c′ , o = k , c′ , places 0 (map fromDirtE o)
pushC1 (kS at 0)      c with pushC dS c
... | k , c′ , o = k , c′ , places 0 (map fromDirtE o)
pushC1 (kZZ at 0)     c with pushZZC c
... | k , c′ , o = k , c′ , places 0 o
-- no rule, and nothing delivers it
pushC1 (kH at 0)      c = ₀ , c , (kH at 0) ∷ []
-- the C box is not on these wires
pushC1 (kH at ₁₊ w)  c = ₀ , c , (kH at ₁₊ w) ∷ []
pushC1 (kS at ₁₊ w)  c = ₀ , c , (kS at ₁₊ w) ∷ []
pushC1 (kX at ₁₊ w)  c = ₀ , c , (kX at ₁₊ w) ∷ []
pushC1 (kZZ at ₁₊ w) c = ₀ , c , (kZZ at ₁₊ w) ∷ []

-- A word of them, consumed from the right as everywhere in §6.
pushCs : List Placed → CBox → ℤ 8 × CBox × List Placed
pushCs []       c = ₀ , c , []
pushCs (g ∷ gs) c with pushCs gs c
... | k₂ , c′ , o₂ with pushC1 g c′
...   | k₁ , c″ , o₁ = k₁ + k₂ , c″ , o₁ ++ o₂

------------------------------------------------------------------------
-- The handoff to the staircase, and what stands in its way
--
-- With pushCs above and PushingChain.push-Chain, the first two thirds
-- of h are in place: a generator becomes a placed gate, crosses the
-- chain, then crosses the C box, all in ℕ-indexed wires.
--
-- The staircase does not take ℕ-indexed wires.  pushS-at, pushH-at and
-- pushZZ-at index their level by a Fin, deliberately: a staircase on
-- ₁₊ n wires admits exactly n+1 levels, and using Fin was what removed
-- the unreachable clause where a wrong answer could hide.
--
-- So the handoff needs to know that a gate leaving the C box is on a
-- wire the staircase actually has.  That is the escape invariant Tower
-- records, and it is true -- Definition 6.1's wire labelling is exactly
-- the claim that dirt stays in range -- but it is not something the
-- types currently know, and converting a ℕ to a Fin without it means
-- inventing an out-of-range case.  Which is the one thing this
-- development has consistently refused to do.
--
-- The way out is to index Placed by the width, so that a gate carries a
-- Fin wire from the start and the chain traversal preserves it by
-- construction rather than by argument.  That is a real change to
-- Placed and to PushingChain, not a patch here, so it is left for a
-- clean pass rather than bolted on at the end of this one.

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
