------------------------------------------------------------------------
-- Presentations of groups
--
-- Normalization (arXiv:1310.6813, §6): dirty gates with their wires.
--
-- Every rule table so far names its dirt by SUBSCRIPT -- H₀, S₁, ZZ₀₁ --
-- which is relative to the box the rule is about.  That is right for
-- transcribing the paper, where each figure concerns one box or one
-- adjacent pair, and it is what lets the tables be checked line by line
-- against the source.
--
-- It stops being enough at the Z-normal chain.  There the traversal is
-- recursive: dirt leaving a layer has to meet the box BELOW it, so a
-- gate emitted at subscript 0 of one box arrives at subscript 1 of the
-- next, and a rule two layers up emits dirt whose eventual wire depends
-- on how far up it was.  Subscripts cannot say that; an absolute wire
-- can.
--
-- So a Placed gate is a kind together with the wire it occupies, and
-- `place` is the one conversion from the tables' subscripts, given the
-- base wire of the box that emitted them.  Doing that conversion once,
-- here, is what keeps it from being spread over sixty-five rules -- the
-- same discipline that kept the paper's qubit numbering out of the
-- tables.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Clifford.Qubit.Selinger.Placed
  (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.List using (List ; [] ; _∷_ ; map)
open import Data.Product using (_×_ ; _,_)

open import ForStdlib.Data.Fin.Mod using (ℤ ; ₀)
open import Notations using (₁₊ ; ₂₊)

open import Examples.Groups.Clifford.Qubit.Selinger.Boxes p-2 p-prime
open import Examples.Groups.Clifford.Qubit.Selinger.Pushing p-2 p-prime
  using ( Dirty ; H₀ ; S₀ ; X₀ ; H₁ ; S₁ ; X₁ ; H₂ ; S₂ ; ZZ₀₁ ; ZZ₁₂
        ; pushHB ; pushS₀B ; pushS₁B ; pushX₁B ; pushZZ₁₂B )

------------------------------------------------------------------------
-- Placed gates

-- The four dirty gates of Definition 6.1, without a wire.
data Kind : Set where
  kH kS kX kZZ : Kind

-- A gate on a wire.  A controlled-Z at wire w spans (w , w+1); the
-- others occupy w alone.
record Placed : Set where
  constructor _at_
  field
    kind : Kind
    wire : ℕ

open Placed public

------------------------------------------------------------------------
-- From subscripts to wires
--
-- The base wire is the lower wire of the box whose rule emitted the
-- dirt, so subscript 0 lands there, subscript 1 one above, subscript 2
-- two above, and a ZZ spans upwards from its own subscript.

place : ℕ → Dirty → Placed
place w H₀   = kH at w
place w S₀   = kS at w
place w X₀   = kX at w
place w H₁   = kH at ₁₊ w
place w S₁   = kS at ₁₊ w
place w X₁   = kX at ₁₊ w
place w H₂   = kH at ₂₊ w
place w S₂   = kS at ₂₊ w
place w ZZ₀₁ = kZZ at w
place w ZZ₁₂ = kZZ at ₁₊ w

places : ℕ → List Dirty → List Placed
places w = map (place w)

------------------------------------------------------------------------
-- A placed gate meeting one B box
--
-- The box sits on (0,1), so the wire decides which rule fires, and the
-- rules decide which wires are possible:
--
--   wire 0    the box's lower wire: commHIB for an H, commSIB for an S
--   wire 1    its upper wire: commISB for an S, commIXB for an X
--   wire 2+   the box is not on that wire, so the gate passes
--
-- A controlled-Z on (1,2) also meets the box, sharing its upper wire:
-- that is commIZZBBI, and it is a one-wire encounter like the others.
-- One on (0,1) is not -- it SPANS the box rather than meeting it on a
-- wire, and is one of PushingZ's two-box rules -- so it must be dealt
-- with by the caller and never reach here.
--
-- PRECONDITION: not (kZZ at 0).  The clause below returns it unchanged,
-- which is wrong; it is a precondition rather than a case.
--
-- An X on wire 0 and an H on wire 1 have no rule and cannot arrive.
-- Every case is written out rather than caught by a wildcard: the
-- wildcard this replaces was silently passing kZZ at 1 through, which
-- looked unreachable and is not -- commIZZBBI is exactly that case, and
-- had not been transcribed at all.

pushB1 : Placed → BBox → ℤ 8 × BBox × List Placed
pushB1 (kH at 0)       b with pushHB b
... | k , b′ , o = k , b′ , places 0 o
pushB1 (kS at 0)       b with pushS₀B b
... | k , b′ , o = k , b′ , places 0 o
pushB1 (kS at ₁₊ 0)   b with pushS₁B b
... | k , b′ , o = k , b′ , places 0 o
pushB1 (kX at ₁₊ 0)   b with pushX₁B b
... | k , b′ , o = k , b′ , places 0 o
pushB1 (kZZ at ₁₊ 0)  b with pushZZ₁₂B b
... | k , b′ , o = k , b′ , places 0 o
-- the box is not on these wires, so the gate passes
pushB1 (kH at ₂₊ w)   b = ₀ , b , (kH at ₂₊ w) ∷ []
pushB1 (kS at ₂₊ w)   b = ₀ , b , (kS at ₂₊ w) ∷ []
pushB1 (kX at ₂₊ w)   b = ₀ , b , (kX at ₂₊ w) ∷ []
pushB1 (kZZ at ₂₊ w)  b = ₀ , b , (kZZ at ₂₊ w) ∷ []
-- no rule, and nothing delivers these
pushB1 (kX at 0)       b = ₀ , b , (kX at 0) ∷ []
pushB1 (kH at ₁₊ 0)   b = ₀ , b , (kH at ₁₊ 0) ∷ []
-- the precondition above: spans the box, handled by PushingZ
pushB1 (kZZ at 0)      b = ₀ , b , (kZZ at 0) ∷ []
