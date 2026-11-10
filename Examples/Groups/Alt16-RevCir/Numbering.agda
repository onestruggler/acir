------------------------------------------------------------------------
-- Presentations of groups
--
-- The numbering of the sixteen states of four wires along the
-- reflected Gray code
--
-- Position i is the state i xor (i >> 1), bit k of it on wire k, so
-- that wire 0 changes most often and two consecutive states differ on
-- one wire.  Vectors list wire 0 first: position 1 is 1000 below, the
-- state with wire 0 set.  enc and dec are the numbering and its
-- inverse, and fin16 takes a statement about the sixteen positions
-- apart into its sixteen cases, for proofs by evaluation at each.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alt16-RevCir.Numbering where

open import Data.Bool.Base using (true ; false)
open import Data.Fin using (Fin ; zero ; suc ; #_)
open import Data.Vec.Base using ([] ; _∷_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Examples.Groups.Alt16-RevCir.Semantics using (Bits)

private
  variable
    ℓ : Level

  pattern O = false
  pattern I = true

  pattern 4+ i = suc (suc (suc (suc i)))
  pattern 8+ i = 4+ (4+ i)
  pattern 12+ i = 8+ (4+ i)

------------------------------------------------------------------------
-- The sixteen positions

fin16 : (P : Fin 16 → Set ℓ) →
        P (# 0) → P (# 1) → P (# 2) → P (# 3) →
        P (# 4) → P (# 5) → P (# 6) → P (# 7) →
        P (# 8) → P (# 9) → P (# 10) → P (# 11) →
        P (# 12) → P (# 13) → P (# 14) → P (# 15) →
        ∀ i → P i
fin16 P p₀ p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ p₁₄ p₁₅ = go
  where
  go : ∀ i → P i
  go zero                        = p₀
  go (suc zero)                  = p₁
  go (suc (suc zero))            = p₂
  go (suc (suc (suc zero)))      = p₃
  go (4+ zero)                   = p₄
  go (4+ (suc zero))             = p₅
  go (4+ (suc (suc zero)))       = p₆
  go (4+ (suc (suc (suc zero)))) = p₇
  go (8+ zero)                   = p₈
  go (8+ (suc zero))             = p₉
  go (8+ (suc (suc zero)))       = p₁₀
  go (8+ (suc (suc (suc zero)))) = p₁₁
  go (12+ zero)                  = p₁₂
  go (12+ (suc zero))            = p₁₃
  go (12+ (suc (suc zero)))      = p₁₄
  go (12+ (suc (suc (suc zero)))) = p₁₅

------------------------------------------------------------------------
-- The numbering

-- The state at a position, the bit of wire 0 first.
enc : Fin 16 → Bits 4
enc = fin16 _
  (O ∷ O ∷ O ∷ O ∷ []) (I ∷ O ∷ O ∷ O ∷ [])
  (I ∷ I ∷ O ∷ O ∷ []) (O ∷ I ∷ O ∷ O ∷ [])
  (O ∷ I ∷ I ∷ O ∷ []) (I ∷ I ∷ I ∷ O ∷ [])
  (I ∷ O ∷ I ∷ O ∷ []) (O ∷ O ∷ I ∷ O ∷ [])
  (O ∷ O ∷ I ∷ I ∷ []) (I ∷ O ∷ I ∷ I ∷ [])
  (I ∷ I ∷ I ∷ I ∷ []) (O ∷ I ∷ I ∷ I ∷ [])
  (O ∷ I ∷ O ∷ I ∷ []) (I ∷ I ∷ O ∷ I ∷ [])
  (I ∷ O ∷ O ∷ I ∷ []) (O ∷ O ∷ O ∷ I ∷ [])

-- The position of a state.
dec : Bits 4 → Fin 16
dec (O ∷ O ∷ O ∷ O ∷ []) = # 0
dec (I ∷ O ∷ O ∷ O ∷ []) = # 1
dec (I ∷ I ∷ O ∷ O ∷ []) = # 2
dec (O ∷ I ∷ O ∷ O ∷ []) = # 3
dec (O ∷ I ∷ I ∷ O ∷ []) = # 4
dec (I ∷ I ∷ I ∷ O ∷ []) = # 5
dec (I ∷ O ∷ I ∷ O ∷ []) = # 6
dec (O ∷ O ∷ I ∷ O ∷ []) = # 7
dec (O ∷ O ∷ I ∷ I ∷ []) = # 8
dec (I ∷ O ∷ I ∷ I ∷ []) = # 9
dec (I ∷ I ∷ I ∷ I ∷ []) = # 10
dec (O ∷ I ∷ I ∷ I ∷ []) = # 11
dec (O ∷ I ∷ O ∷ I ∷ []) = # 12
dec (I ∷ I ∷ O ∷ I ∷ []) = # 13
dec (I ∷ O ∷ O ∷ I ∷ []) = # 14
dec (O ∷ O ∷ O ∷ I ∷ []) = # 15

dec-enc : ∀ i → dec (enc i) ≡ i
dec-enc = fin16 _
  refl refl refl refl refl refl refl refl
  refl refl refl refl refl refl refl refl

enc-dec : ∀ x → enc (dec x) ≡ x
enc-dec (O ∷ O ∷ O ∷ O ∷ []) = refl
enc-dec (I ∷ O ∷ O ∷ O ∷ []) = refl
enc-dec (I ∷ I ∷ O ∷ O ∷ []) = refl
enc-dec (O ∷ I ∷ O ∷ O ∷ []) = refl
enc-dec (O ∷ I ∷ I ∷ O ∷ []) = refl
enc-dec (I ∷ I ∷ I ∷ O ∷ []) = refl
enc-dec (I ∷ O ∷ I ∷ O ∷ []) = refl
enc-dec (O ∷ O ∷ I ∷ O ∷ []) = refl
enc-dec (O ∷ O ∷ I ∷ I ∷ []) = refl
enc-dec (I ∷ O ∷ I ∷ I ∷ []) = refl
enc-dec (I ∷ I ∷ I ∷ I ∷ []) = refl
enc-dec (O ∷ I ∷ I ∷ I ∷ []) = refl
enc-dec (O ∷ I ∷ O ∷ I ∷ []) = refl
enc-dec (I ∷ I ∷ O ∷ I ∷ []) = refl
enc-dec (I ∷ O ∷ O ∷ I ∷ []) = refl
enc-dec (O ∷ O ∷ O ∷ I ∷ []) = refl
