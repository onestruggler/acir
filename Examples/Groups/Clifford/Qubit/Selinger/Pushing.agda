------------------------------------------------------------------------
-- Presentations of groups
--
-- Normalization (arXiv:1310.6813, §6): pushing dirt through the
-- two-qubit boxes.
--
-- Rewrite.agda handles one qubit, where the boxes are A, C, E.  This
-- module treats the B and D boxes, which span two adjacent wires, in the
-- cases where a single dirty gate meets a single box.
--
-- Figures 3-7 split in two, and the split is worth naming because it is
-- what the rest of §6 turns on:
--
--   LOCAL rules -- a dirty gate meets one box.  These are the families
--   below: commHIB, commSIB, commISB, commIXB into a B box, and
--   altIHDD, altISDD, altSIDD, altZZDD into a D box.  A local rule
--   rewrites one box and emits dirt to its right.
--
--   TWO-BOX rules -- a controlled-Z spans two wires and therefore meets
--   the boxes on BOTH of them at once, so it consumes an adjacent pair:
--   commZZAI, commZZIABB (a CZ over A and the B above it),
--   commZZIIBBBBI (over two B boxes) and altIZZDDIIDD (over two D
--   boxes).  Those are not here.
--
-- Note which dirt each family emits.  The D families are closed: they
-- produce only H and S on the box's own two wires, never a
-- controlled-Z.  The B families are not -- commISB emits a ZZ on the
-- box's own pair -- which is why Dirty carries a ZZ₀₁ constructor and
-- why the B side is the one that keeps generating work.
--
-- Wire numbering follows the paper, as the rule names do: the subscript
-- on H₀, S₁ and so on is the paper's qubit number, which is this
-- development's wire number too (see Boxes).  So subscript 0 is a box's
-- lower, un-shifted wire and subscript 1 the one above it.
--
-- Transcribed from the arXiv source of Figures 3-7, each rule carrying
-- its phase and word, e.g.
--
--   % (0,[Hx 0,B 3 0 1]) = % (0,[B 3 0 1,Xx 0,Sx 1,Sx 1,Sx 1,Hx 1,Sx 1])
--
-- i.e. H₀·B₃ = B₃·X₀·S₁³·H₁·S₁.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Clifford.Qubit.Selinger.Pushing
  (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Product using (_×_ ; _,_)

-- Only ₀ is needed: every rule in this module is phase-free.  Phases
-- enter §6 solely through the A-box rules (Rewrite) and the two-box
-- controlled-Z families, which are not here.
open import ForStdlib.Data.Fin.Mod using (ℤ ; ₀)

open import Examples.Groups.Clifford.Qubit.Selinger.Boxes p-2 p-prime

------------------------------------------------------------------------
-- Dirt around a two-qubit box
--
-- Relative to the box: wire 0 is its lower wire, wire 1 its upper.  The
-- controlled-Z spans the pair.  Definition 6.1 permits no other dirt
-- here, and the rules below emit no other.

-- Dirt that stays within the box's own pair.  Sixty-six of the
-- sixty-nine rules emit only this.
data Dirty : Set where
  H₀ S₀ X₀ : Dirty
  H₁ S₁ X₁ : Dirty
  ZZ₀₁     : Dirty

-- Dirt that also reaches one wire ABOVE the pair.  Exactly three rules
-- emit it -- pushZZ₁₂B below, PushingZ's pushZZ-BB and PushingD's
-- pushZZ-DD -- and each of them fires only when that wire is known to
-- exist, either because the incoming controlled-Z sits on it or because
-- a second box occupies it.
--
-- The split is what lets a gate be placed on a wire whose range the
-- types can check: a rule emitting only Dirty needs no headroom beyond
-- its own pair, while one emitting Dirty⁺ needs a wire more, and the
-- two can no longer be confused.
-- The constructor names are shared with Dirty deliberately: the rule
-- tables then read the same whichever alphabet they emit into, and
-- Agda picks by the expected type.  Only the three signatures differ.
data Dirty⁺ : Set where
  H₀ S₀ X₀  : Dirty⁺
  H₁ S₁ X₁  : Dirty⁺
  H₂ S₂     : Dirty⁺
  ZZ₀₁ ZZ₁₂ : Dirty⁺

------------------------------------------------------------------------
-- Into a B box
--
-- The dirty gate is the one immediately to the box's left; the result is
-- a phase, the new box, and the dirt emerging on its right.

-- commHIB: H on the box's lower wire (qubit 0).
pushHB : BBox → ℤ 8 × BBox × List Dirty
pushHB b₁ = ₀ , b₁ , H₁ ∷ []
pushHB b₂ = ₀ , b₄ , []
pushHB b₃ = ₀ , b₃ , X₀ ∷ S₁ ∷ S₁ ∷ S₁ ∷ H₁ ∷ S₁ ∷ []
pushHB b₄ = ₀ , b₂ , []

-- commSIB: S on the box's lower wire.
pushS₀B : BBox → ℤ 8 × BBox × List Dirty
pushS₀B b₁ = ₀ , b₁ , H₁ ∷ S₁ ∷ H₁ ∷ []
pushS₀B b₂ = ₀ , b₃ , X₀ ∷ S₁ ∷ S₁ ∷ S₁ ∷ H₁ ∷ S₁ ∷ []
pushS₀B b₃ = ₀ , b₂ , S₁ ∷ H₁ ∷ S₁ ∷ []
pushS₀B b₄ = ₀ , b₄ , H₁ ∷ S₁ ∷ H₁ ∷ []

-- commISB: S on the box's upper wire.  This is the family that emits a
-- controlled-Z, so B boxes keep the normalization going.
pushS₁B : BBox → ℤ 8 × BBox × List Dirty
pushS₁B b₁ = ₀ , b₁ , S₀ ∷ []
pushS₁B b₂ = ₀ , b₂ , H₁ ∷ ZZ₀₁ ∷ S₀ ∷ S₁ ∷ H₁ ∷ []
pushS₁B b₃ = ₀ , b₃ , H₁ ∷ ZZ₀₁ ∷ S₀ ∷ S₁ ∷ H₁ ∷ []
pushS₁B b₄ = ₀ , b₄ , H₁ ∷ ZZ₀₁ ∷ S₀ ∷ S₁ ∷ H₁ ∷ []

-- commIZZBBI: a controlled-Z on (1,2), which shares the box's UPPER
-- wire and so meets it -- on one wire only, unlike the controlled-Z on
-- the box's own pair, which spans it and is PushingZ's business.  The
-- box never changes; what comes out is a long word of controlled-Zs and
-- H gates on both pairs.
pushZZ₁₂B : BBox → ℤ 8 × BBox × List Dirty⁺
pushZZ₁₂B b₁ = ₀ , b₁
             , ZZ₀₁ ∷ H₁ ∷ ZZ₁₂ ∷ H₁ ∷ ZZ₀₁ ∷ H₁ ∷ ZZ₁₂ ∷ H₁ ∷ []
pushZZ₁₂B b₂ = ₀ , b₂ , ZZ₀₁ ∷ H₁ ∷ ZZ₁₂ ∷ H₁ ∷ ZZ₀₁ ∷ []
pushZZ₁₂B b₃ = ₀ , b₃ , ZZ₀₁ ∷ H₁ ∷ ZZ₁₂ ∷ H₁ ∷ ZZ₀₁ ∷ []
pushZZ₁₂B b₄ = ₀ , b₄ , ZZ₀₁ ∷ H₁ ∷ ZZ₁₂ ∷ H₁ ∷ ZZ₀₁ ∷ []

-- commIXB: X on the box's upper wire.  Uniformly, the box is unchanged
-- and the X drops to the lower wire.
pushX₁B : BBox → ℤ 8 × BBox × List Dirty
pushX₁B b₁ = ₀ , b₁ , X₀ ∷ []
pushX₁B b₂ = ₀ , b₂ , X₀ ∷ []
pushX₁B b₃ = ₀ , b₃ , X₀ ∷ []
pushX₁B b₄ = ₀ , b₄ , X₀ ∷ []

------------------------------------------------------------------------
-- Into a D box
--
-- These four families are closed: no rule emits a controlled-Z, so dirt
-- entering the X-normal staircase leaves it as H and S alone.

-- altIHDD: H on the box's upper wire (qubit 1).
pushH₁D : DBox → ℤ 8 × DBox × List Dirty
pushH₁D d₁ = ₀ , d₁ , H₀ ∷ []
pushH₁D d₂ = ₀ , d₄ , []
pushH₁D d₃ = ₀ , d₃ , S₀ ∷ S₀ ∷ S₀ ∷ H₀ ∷ S₀ ∷ S₁ ∷ S₁ ∷ []
pushH₁D d₄ = ₀ , d₂ , []

-- altISDD: S on the box's upper wire.
pushS₁D : DBox → ℤ 8 × DBox × List Dirty
pushS₁D d₁ = ₀ , d₁ , H₀ ∷ S₀ ∷ H₀ ∷ []
pushS₁D d₂ = ₀ , d₃ , S₀ ∷ S₀ ∷ S₀ ∷ H₀ ∷ S₀ ∷ S₁ ∷ S₁ ∷ []
pushS₁D d₃ = ₀ , d₂ , S₀ ∷ H₀ ∷ S₀ ∷ []
pushS₁D d₄ = ₀ , d₄ , H₀ ∷ S₀ ∷ H₀ ∷ []

-- altSIDD: S on the box's lower wire.  Uniformly, the box is unchanged
-- and the S rises to the upper wire.
pushS₀D : DBox → ℤ 8 × DBox × List Dirty
pushS₀D d₁ = ₀ , d₁ , S₁ ∷ []
pushS₀D d₂ = ₀ , d₂ , S₁ ∷ []
pushS₀D d₃ = ₀ , d₃ , S₁ ∷ []
pushS₀D d₄ = ₀ , d₄ , S₁ ∷ []

-- altZZDD: a controlled-Z on the box's own pair.  This one IS local --
-- the CZ meets a single D box -- unlike the CZ families over adjacent
-- pairs of boxes.  d₁ and d₄ simply swap.
pushZZD : DBox → ℤ 8 × DBox × List Dirty
pushZZD d₁ = ₀ , d₄ , []
pushZZD d₂ = ₀ , d₃ , S₀ ∷ S₀ ∷ S₀ ∷ H₀ ∷ S₁ ∷ S₁ ∷ S₁ ∷ []
pushZZD d₃ = ₀ , d₂ , H₀ ∷ S₀ ∷ S₁ ∷ []
pushZZD d₄ = ₀ , d₁ , []

------------------------------------------------------------------------
-- Into a C box, from the wire below it
--
-- commZZCI: a controlled-Z whose lower wire carries the C box (the
-- paper's ZZx 0 1 with C on qubit 0).  Local, and the only C rule not
-- already in Rewrite.

pushZZC : CBox → ℤ 8 × CBox × List Dirty
pushZZC c₁ = ₀ , c₁ , ZZ₀₁ ∷ []
pushZZC c₂ = ₀ , c₂ , ZZ₀₁ ∷ S₁ ∷ S₁ ∷ []
