------------------------------------------------------------------------
-- Presentations of groups
--
-- The three gadget blocks
--
-- The gadgets of the affine decoding act on two basis vectors p, q as
-- the 2 × 2 blocks iZ (the phase pair), XZ (the signed exchange) and
-- γ⁻¹ [[−1 , −i] , [1 , −i]] = K_[q,p] · i_[q]⁻¹ (the hybrid with its
-- pair exchanged), and as the identity elsewhere.  On four wires the
-- canonical pair is 0 and e₀.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Sem.Blocks where

open import Data.Bool using (true ; false)
open import Data.Vec using ([] ; _∷_)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Five.Sem.TL using (Blk ; blk)

data Kind : Set where
  kpp krot kki : Kind

blkOf : Kind → Blk
blkOf kpp  = blk 0 ⅈ 0# 0# -ⅈ
blkOf krot = blk 0 0# -1# 1# 0#
blkOf kki  = blk 1 -1# -ⅈ 1# -ⅈ

o₄ e₄ : Bits 4
o₄ = false ∷ false ∷ false ∷ false ∷ []
e₄ = true ∷ false ∷ false ∷ false ∷ []
