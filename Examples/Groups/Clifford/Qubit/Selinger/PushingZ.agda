------------------------------------------------------------------------
-- Presentations of groups
--
-- Normalization (arXiv:1310.6813, §6): a controlled-Z meeting the
-- Z-normal chain.
--
-- These are the two-box rules.  A controlled-Z spans two wires, so it
-- meets the boxes on BOTH of them and consumes an adjacent pair; the
-- rules therefore cannot be stated per box, as the local ones of
-- Pushing are.
--
-- The pair it meets is determined by where the CZ sits in the Z-normal
-- chain of Definition 4.3, and the three possibilities are exactly the
-- paper's three macros:
--
--   commZZAI       ZZ on (0,1) meeting an A on qubit 0, with no B box
--                  -- the chain stops at the A.
--   commZZIABB     ZZ on (0,1) meeting a B on the pair and the A on
--                  qubit 1, directly above it.
--   commZZIIBBBBI  ZZ on (0,1) meeting a B on the pair and another B
--                  on (1,2).
--
-- Against Normal.Chain -- either the A sits on the un-shifted wire, or a
-- B holds the bottom pair and the rest stands above -- that is exactly
-- the three-way split on the chain's first two layers:
--
--   inj₁ a                    commZZAI
--   inj₂ (b , inj₁ a)         commZZIABB
--   inj₂ (b , inj₂ (b′ , _))  commZZIIBBBBI
--
-- and it is not a coincidence: the chain is the data the paper's
-- picture records, so a rule consuming two boxes consumes two layers.
--
-- This rests on qubit j being wire j, which the L(n) coordinates confirm
-- once they are read as y-coordinates rather than qubit numbers -- the
-- C box sits on qubit 0 and the B boxes run away from it through (0,1),
-- (1,2), ..., which is Chain exactly.  See the note in Boxes; reading
-- those coordinates the other way once cost two commits.
--
-- The chain CHANGES LENGTH.  commZZAI can turn an A on the bottom wire
-- into a B with the A above it, and commZZIABB can do the reverse, so
-- the result types below are sums saying which happened.  That is why
-- these rules are stated on the chain rather than on a box: the box
-- alone does not determine the shape of the answer.
--
-- Transcribed from the arXiv source, e.g.
--
--   % (0,[ZZx 0 1,A 2 1,B 3 0 1])
--     = % (1,[A 3 1,B 2 0 1,Xx 0,Hx 1,ZZx 0 1,Sx 0,Sx 0,Sx 0])
--
-- i.e. ZZ·A₂·B₃ = ω·A₃·B₂·X₀·H₁·ZZ·S₀³, where the A and B on each side
-- are the two chain layers and the rest is dirt.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Clifford.Qubit.Selinger.PushingZ
  (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Product using (_×_ ; _,_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)

-- ForStdlib.Data.Fin.Mod re-exports only ₀-₄ of the numeral patterns,
-- and these rules carry phases 6 and 7, so the numerals come from
-- Notations and only ℤ from Mod.
open import ForStdlib.Data.Fin.Mod using (ℤ)
open import Notations using (₀ ; ₁ ; ₆ ; ₇)

open import Examples.Groups.Clifford.Qubit.Selinger.Boxes p-2 p-prime
open import Examples.Groups.Clifford.Qubit.Selinger.Pushing p-2 p-prime
  using ( Dirty ; Dirty⁺
        ; H₀ ; S₀ ; X₀ ; H₁ ; S₁ ; X₁ ; H₂ ; S₂ ; ZZ₀₁ ; ZZ₁₂ )

------------------------------------------------------------------------
-- The top of a chain, after the rewrite
--
-- Either the A box sits on the un-shifted wire with no B below it, or a
-- B box holds the bottom pair with the A directly above.  These are the
-- two shapes Normal.Chain offers at its first two layers, and a rule
-- may return either whatever it was given.

Top : Set
Top = ABox ⊎ (BBox × ABox)

------------------------------------------------------------------------
-- commZZAI: the chain is a bare A on the CZ's lower wire
--
-- A₁ commutes past.  The other two grow the chain by a B box, so the
-- Z-normal circuit gets longer -- the one place in §6 where that
-- happens.

pushZZ-A : ABox → ℤ 8 × Top × List Dirty
pushZZ-A a₁ = ₀ , inj₁ a₁ , ZZ₀₁ ∷ []
pushZZ-A a₂ = ₀ , inj₂ (b₂ , a₁) , ZZ₀₁ ∷ H₁ ∷ []
pushZZ-A a₃ = ₀ , inj₂ (b₃ , a₁)
            , H₁ ∷ S₁ ∷ H₁ ∷ ZZ₀₁ ∷ S₀ ∷ S₀ ∷ S₀ ∷ H₁ ∷ []

------------------------------------------------------------------------
-- commZZIABB: a B on the CZ's pair, the A directly above
--
-- Three of the twelve shrink the chain, dropping the A to the
-- un-shifted wire; the rest keep both layers.  Four carry a phase.

pushZZ-AB : ABox → BBox → ℤ 8 × Top × List Dirty
pushZZ-AB a₁ b₁ = ₀ , inj₂ (b₁ , a₁) , H₁ ∷ ZZ₀₁ ∷ H₁ ∷ []
pushZZ-AB a₁ b₂ = ₀ , inj₁ a₂        , H₁ ∷ ZZ₀₁ ∷ []
pushZZ-AB a₁ b₃ = ₇ , inj₁ a₃        , H₁ ∷ ZZ₀₁ ∷ S₀ ∷ S₁ ∷ H₁ ∷ S₁ ∷ []
pushZZ-AB a₁ b₄ = ₀ , inj₂ (b₄ , a₁) , H₁ ∷ ZZ₀₁ ∷ S₁ ∷ S₁ ∷ H₁ ∷ []
pushZZ-AB a₂ b₁ = ₀ , inj₂ (b₄ , a₂) , []
pushZZ-AB a₂ b₂ = ₆ , inj₂ (b₃ , a₃)
                , H₁ ∷ ZZ₀₁ ∷ S₀ ∷ S₁ ∷ S₁ ∷ H₁ ∷ S₁ ∷ []
pushZZ-AB a₂ b₃ = ₁ , inj₂ (b₂ , a₃)
                , X₀ ∷ H₁ ∷ ZZ₀₁ ∷ S₀ ∷ S₀ ∷ S₀ ∷ []
pushZZ-AB a₂ b₄ = ₀ , inj₂ (b₁ , a₂) , []
pushZZ-AB a₃ b₁ = ₀ , inj₂ (b₄ , a₃) , H₁ ∷ ZZ₀₁ ∷ S₁ ∷ H₁ ∷ []
pushZZ-AB a₃ b₂ = ₁ , inj₂ (b₃ , a₂)
                , X₀ ∷ ZZ₀₁ ∷ S₀ ∷ S₀ ∷ S₀ ∷ S₁ ∷ S₁ ∷ H₁ ∷ []
pushZZ-AB a₃ b₃ = ₁ , inj₂ (b₂ , a₂)
                , H₁ ∷ S₁ ∷ H₁ ∷ ZZ₀₁ ∷ S₀ ∷ S₀ ∷ S₀ ∷ S₁ ∷ S₁ ∷ S₁ ∷ H₁ ∷ []
pushZZ-AB a₃ b₄ = ₀ , inj₂ (b₁ , a₃)
                , H₁ ∷ ZZ₀₁ ∷ S₁ ∷ S₁ ∷ S₁ ∷ H₁ ∷ []

------------------------------------------------------------------------
-- commZZIIBBBBI: a B on the CZ's pair, another B above
--
-- Both boxes may change and the chain keeps its length, so no sum is
-- needed here.  The dirt reaches wire 2 and carries a controlled-Z on
-- the pair above, which is what sends the rewrite further up the chain.
--
-- The arguments are (upper , lower): the paper writes ZZ·B_j¹²·B_j'⁰¹.

pushZZ-BB : BBox → BBox → ℤ 8 × (BBox × BBox) × List Dirty⁺
pushZZ-BB b₁ b₁ = ₀ , (b₁ , b₁) , H₁ ∷ H₂ ∷ ZZ₁₂ ∷ H₁ ∷ H₂ ∷ []
pushZZ-BB b₁ b₂ = ₀ , (b₄ , b₂) , H₂ ∷ ZZ₁₂ ∷ H₂ ∷ []
pushZZ-BB b₁ b₃ = ₇ , (b₄ , b₃)
                , H₂ ∷ H₁ ∷ S₁ ∷ H₁ ∷ ZZ₁₂ ∷ S₁ ∷ H₁ ∷ S₁ ∷ H₂ ∷ []
pushZZ-BB b₁ b₄ = ₀ , (b₁ , b₄) , H₁ ∷ H₂ ∷ ZZ₁₂ ∷ H₁ ∷ H₂ ∷ []
pushZZ-BB b₂ b₁ = ₀ , (b₂ , b₄) , H₁ ∷ ZZ₁₂ ∷ H₁ ∷ []
pushZZ-BB b₂ b₂ = ₆ , (b₃ , b₃)
                , H₁ ∷ S₁ ∷ H₁ ∷ H₂ ∷ S₂ ∷ H₂ ∷ ZZ₁₂ ∷ S₁ ∷ S₂ ∷ []
pushZZ-BB b₂ b₃ = ₇ , (b₃ , b₂)
                , H₂ ∷ S₂ ∷ H₂ ∷ ZZ₁₂ ∷ X₀ ∷ H₁ ∷ S₁ ∷ S₂ ∷ []
pushZZ-BB b₂ b₄ = ₀ , (b₂ , b₁) , H₁ ∷ ZZ₁₂ ∷ H₁ ∷ []
pushZZ-BB b₃ b₁ = ₇ , (b₃ , b₄)
                , H₁ ∷ H₂ ∷ S₂ ∷ H₂ ∷ ZZ₁₂ ∷ H₁ ∷ S₂ ∷ H₂ ∷ S₂ ∷ []
pushZZ-BB b₃ b₂ = ₇ , (b₂ , b₃)
                , H₁ ∷ S₁ ∷ H₁ ∷ ZZ₁₂ ∷ X₀ ∷ S₁ ∷ H₂ ∷ S₂ ∷ []
pushZZ-BB b₃ b₃ = ₀ , (b₂ , b₂) , ZZ₁₂ ∷ H₁ ∷ S₁ ∷ H₂ ∷ S₂ ∷ []
pushZZ-BB b₃ b₄ = ₇ , (b₃ , b₁)
                , H₁ ∷ H₂ ∷ S₂ ∷ H₂ ∷ ZZ₁₂ ∷ H₁ ∷ S₂ ∷ H₂ ∷ S₂ ∷ []
pushZZ-BB b₄ b₁ = ₀ , (b₄ , b₁) , H₁ ∷ H₂ ∷ ZZ₁₂ ∷ H₁ ∷ H₂ ∷ []
pushZZ-BB b₄ b₂ = ₀ , (b₁ , b₂) , H₂ ∷ ZZ₁₂ ∷ H₂ ∷ []
pushZZ-BB b₄ b₃ = ₇ , (b₁ , b₃)
                , H₂ ∷ H₁ ∷ S₁ ∷ H₁ ∷ ZZ₁₂ ∷ S₁ ∷ H₁ ∷ S₁ ∷ H₂ ∷ []
pushZZ-BB b₄ b₄ = ₀ , (b₄ , b₄) , H₁ ∷ H₂ ∷ ZZ₁₂ ∷ H₁ ∷ H₂ ∷ []
