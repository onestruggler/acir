------------------------------------------------------------------------
-- Presentations of groups
--
-- Equations on one wire, derived from the rules
--
-- The one-wire rules — iI⁴ = ε, S⁴ = ε, K² = iI³, (S K)³ = iI³, and
-- iI central — present a group of order 96, U₂(ℤ[½,i]): a Knuth–Bendix
-- completion of them (scratchpad kb.py, gen1.py) terminates with 26
-- rules and 96 irreducible words.  The equations below are what the
-- one-qubit back-and-forth argument (OneQubit) needs, with X = K S² K iI:
-- that X is an involution, that X S X S = iI, and the decodings of the
-- relations of Bian and Selinger on two indices.  Each is derived by
-- rewriting both sides to their common normal form with the completed
-- system, every rule of which is derived from the ones before; the
-- derivations are machine-generated (Derivation for their format).
--
-- They are stated on wire 0 of any width, so that they apply on the
-- bottom wire of a wider circuit, and on any other wire through cong↑.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.Lemmas.OneWire {n : ℕ} where

open import Data.List using (List ; [] ; _∷_)
open import Notations using (₁₊)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Syntactics
open PB ((₁₊ n) VRel,_===_) using (_≈_ ; refl ; sym ; axiom)
open import Examples.Groups.Clifford+CS.Derivation ((₁₊ n) VRel,_===_)

private
  r0 : from-list (I-gen ∷ I-gen ∷ I-gen ∷ I-gen ∷ []) ≈ from-list []
  r0 = ⌊ axiom (srel order-I) ⌋

  r1 : from-list (S-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) ≈ from-list []
  r1 = ⌊ axiom (srel order-S) ⌋

  r2 : from-list (I-gen ∷ I-gen ∷ I-gen ∷ []) ≈ from-list (K-gen ∷ K-gen ∷ [])
  r2 = sym (⌊ axiom (srel order-K) ⌋)

  r3 : from-list (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ []) ≈ from-list (I-gen ∷ I-gen ∷ I-gen ∷ [])
  r3 = ⌊ axiom (srel order-SK) ⌋

  r4 : from-list (S-gen ∷ I-gen ∷ []) ≈ from-list (I-gen ∷ S-gen ∷ [])
  r4 = ⌊ comm₀ I-gate S-gen ⌋

  r5 : from-list (K-gen ∷ I-gen ∷ []) ≈ from-list (I-gen ∷ K-gen ∷ [])
  r5 = ⌊ comm₀ I-gate K-gen ⌋

  r6 : from-list (K-gen ∷ K-gen ∷ K-gen ∷ K-gen ∷ []) ≈ from-list (I-gen ∷ I-gen ∷ [])
  r6 =
    ctx [] (K-gen ∷ K-gen ∷ []) (I-gen ∷ I-gen ∷ I-gen ∷ []) (K-gen ∷ K-gen ∷ []) (sym r2)
    ⨾ ctx (I-gen ∷ I-gen ∷ I-gen ∷ []) (K-gen ∷ K-gen ∷ []) (I-gen ∷ I-gen ∷ I-gen ∷ []) [] (sym r2)
    ⨾ ctx [] (I-gen ∷ I-gen ∷ I-gen ∷ I-gen ∷ []) [] (I-gen ∷ I-gen ∷ []) r0

  r8 : from-list (I-gen ∷ K-gen ∷ K-gen ∷ []) ≈ from-list []
  r8 =
    ctx [] (I-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ []) (K-gen ∷ []) (sym r5)
    ⨾ ctx (K-gen ∷ []) (I-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ []) [] (sym r5)
    ⨾ ctx [] (K-gen ∷ K-gen ∷ []) (I-gen ∷ I-gen ∷ I-gen ∷ []) (I-gen ∷ []) (sym r2)
    ⨾ ctx [] (I-gen ∷ I-gen ∷ I-gen ∷ I-gen ∷ []) [] [] r0

  r10 : from-list (K-gen ∷ K-gen ∷ S-gen ∷ []) ≈ from-list (S-gen ∷ K-gen ∷ K-gen ∷ [])
  r10 =
    ctx [] (K-gen ∷ K-gen ∷ []) (I-gen ∷ I-gen ∷ I-gen ∷ []) (S-gen ∷ []) (sym r2)
    ⨾ ctx (I-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) [] (sym r4)
    ⨾ ctx (I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ []) (sym r4)
    ⨾ ctx [] (I-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ I-gen ∷ []) (sym r4)
    ⨾ ctx (S-gen ∷ []) (I-gen ∷ I-gen ∷ I-gen ∷ []) (K-gen ∷ K-gen ∷ []) [] r2

  r11 : from-list (I-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) ≈ from-list (I-gen ∷ I-gen ∷ K-gen ∷ [])
  r11 =
    ctx (I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (sym r4)
    ⨾ ctx (I-gen ∷ S-gen ∷ []) (I-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ []) (sym r5)
    ⨾ ctx (I-gen ∷ S-gen ∷ K-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (K-gen ∷ S-gen ∷ []) (sym r4)
    ⨾ ctx (I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (I-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ []) (S-gen ∷ []) (sym r5)
    ⨾ ctx (I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) [] (sym r4)
    ⨾ ctx [] (I-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ I-gen ∷ []) (sym r4)
    ⨾ ctx (S-gen ∷ []) (I-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ I-gen ∷ []) (sym r5)
    ⨾ ctx (S-gen ∷ K-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (K-gen ∷ S-gen ∷ I-gen ∷ []) (sym r4)
    ⨾ ctx (S-gen ∷ K-gen ∷ S-gen ∷ []) (I-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ []) (S-gen ∷ I-gen ∷ []) (sym r5)
    ⨾ ctx (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ []) (sym r4)
    ⨾ ctx (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (I-gen ∷ I-gen ∷ []) (K-gen ∷ K-gen ∷ K-gen ∷ K-gen ∷ []) [] (sym r6)
    ⨾ ctx [] (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ []) (I-gen ∷ I-gen ∷ I-gen ∷ []) (K-gen ∷ K-gen ∷ K-gen ∷ []) r3
    ⨾ ctx [] (I-gen ∷ I-gen ∷ I-gen ∷ []) (K-gen ∷ K-gen ∷ []) (K-gen ∷ K-gen ∷ K-gen ∷ []) r2
    ⨾ ctx [] (K-gen ∷ K-gen ∷ K-gen ∷ K-gen ∷ []) (I-gen ∷ I-gen ∷ []) (K-gen ∷ []) r6

  r13 : from-list (I-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) ≈ from-list (S-gen ∷ [])
  r13 =
    ctx [] (I-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (K-gen ∷ K-gen ∷ []) (sym r4)
    ⨾ ctx (S-gen ∷ []) (I-gen ∷ K-gen ∷ K-gen ∷ []) [] [] r8

  r14 : from-list (I-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) ≈ from-list (K-gen ∷ S-gen ∷ [])
  r14 =
    ctx (I-gen ∷ K-gen ∷ []) (S-gen ∷ K-gen ∷ K-gen ∷ []) (K-gen ∷ K-gen ∷ S-gen ∷ []) [] (sym r10)
    ⨾ ctx [] (I-gen ∷ K-gen ∷ K-gen ∷ []) [] (K-gen ∷ S-gen ∷ []) r8

  r16 : from-list (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) ≈ from-list (K-gen ∷ [])
  r16 =
    ctx [] [] (I-gen ∷ K-gen ∷ K-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (sym r8)
    ⨾ ctx [] (I-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (sym r5)
    ⨾ ctx (K-gen ∷ []) (I-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (sym r5)
    ⨾ ctx [] (K-gen ∷ K-gen ∷ []) (I-gen ∷ I-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (sym r2)
    ⨾ ctx (I-gen ∷ I-gen ∷ []) (I-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (I-gen ∷ I-gen ∷ K-gen ∷ []) [] r11
    ⨾ ctx [] (I-gen ∷ I-gen ∷ I-gen ∷ []) (K-gen ∷ K-gen ∷ []) (I-gen ∷ K-gen ∷ []) r2
    ⨾ ctx (K-gen ∷ []) (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) (K-gen ∷ []) r5
    ⨾ ctx [] (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) (K-gen ∷ K-gen ∷ []) r5
    ⨾ ctx [] (I-gen ∷ K-gen ∷ K-gen ∷ []) [] (K-gen ∷ []) r8

  r17 : from-list (I-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) ≈ from-list (S-gen ∷ S-gen ∷ [])
  r17 =
    ctx [] (I-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (S-gen ∷ K-gen ∷ K-gen ∷ []) (sym r4)
    ⨾ ctx (S-gen ∷ []) (I-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (S-gen ∷ []) [] r13

  r18 : from-list (I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) ≈ from-list (S-gen ∷ K-gen ∷ S-gen ∷ [])
  r18 =
    ctx [] (I-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (sym r4)
    ⨾ ctx (S-gen ∷ []) (I-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (K-gen ∷ S-gen ∷ []) [] r14

  r20 : from-list (I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) ≈ from-list (K-gen ∷ S-gen ∷ S-gen ∷ [])
  r20 =
    ctx (I-gen ∷ K-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ K-gen ∷ []) (K-gen ∷ K-gen ∷ S-gen ∷ []) [] (sym r10)
    ⨾ ctx [] (I-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (K-gen ∷ S-gen ∷ []) (S-gen ∷ []) r14

  r21 : from-list (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) ≈ from-list (S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ [])
  r21 =
    ctx [] [] (S-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (sym r1)
    ⨾ ctx (S-gen ∷ S-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (K-gen ∷ []) [] r16

  r22 : from-list (I-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) ≈ from-list (S-gen ∷ S-gen ∷ S-gen ∷ [])
  r22 =
    ctx [] (I-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (sym r4)
    ⨾ ctx (S-gen ∷ []) (I-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (S-gen ∷ S-gen ∷ []) [] r17

  r23 : from-list (I-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) ≈ from-list (S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ [])
  r23 =
    ctx [] (I-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (sym r4)
    ⨾ ctx (S-gen ∷ []) (I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ []) [] r18

  r24 : from-list (I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) ≈ from-list (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ [])
  r24 =
    ctx [] (I-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (sym r4)
    ⨾ ctx (S-gen ∷ []) (I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ []) [] r20

  r28 : from-list (I-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) ≈ from-list (S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ [])
  r28 =
    ctx [] (I-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (sym r4)
    ⨾ ctx (S-gen ∷ []) (I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ []) [] r24

  r33 : from-list (K-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) ≈ from-list (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ [])
  r33 =
    ctx (K-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) [] (sym r21)
    ⨾ ctx [] (K-gen ∷ K-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ K-gen ∷ []) (K-gen ∷ S-gen ∷ []) r10
    ⨾ ctx (S-gen ∷ K-gen ∷ []) (K-gen ∷ K-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ K-gen ∷ []) [] r10

  r34 : from-list (I-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) ≈ from-list (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ [])
  r34 =
    ctx (I-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ []) (sym r21)
    ⨾ ctx (I-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) [] (sym r21)
    ⨾ ctx [] (I-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (K-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ []) r14

  r35 : from-list (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) ≈ from-list (I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ [])
  r35 =
    ctx [] (S-gen ∷ K-gen ∷ S-gen ∷ []) (I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ []) (sym r18)
    ⨾ ctx (I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) [] r21
    ⨾ ctx (I-gen ∷ S-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ []) r21
    ⨾ ctx (I-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) [] (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) r1

  r37 : from-list (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) ≈ from-list (S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ [])
  r37 =
    ctx [] (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ []) (I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (S-gen ∷ []) (sym r24)
    ⨾ ctx (I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ []) (K-gen ∷ K-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ K-gen ∷ []) [] r10
    ⨾ ctx (I-gen ∷ S-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (K-gen ∷ []) r33
    ⨾ ctx [] (I-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (K-gen ∷ []) r23

  r38 : from-list (I-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) ≈ from-list (S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ [])
  r38 =
    ctx (I-gen ∷ []) (I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ []) (sym r35)
    ⨾ ctx (I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) [] (sym r21)
    ⨾ ctx [] (I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ []) r24
    ⨾ ctx [] (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ []) (K-gen ∷ S-gen ∷ []) r37
    ⨾ ctx (S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (K-gen ∷ K-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ K-gen ∷ []) [] r10

  r40 : from-list (K-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) ≈ from-list (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ [])
  r40 =
    ctx [] [] (S-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) (sym r1)
    ⨾ ctx (S-gen ∷ S-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ []) [] r37
    ⨾ ctx [] (S-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) [] (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ []) r1

  r42 : from-list (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) ≈ from-list (I-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ [])
  r42 =
    ctx [] [] (I-gen ∷ K-gen ∷ K-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (sym r8)
    ⨾ ctx [] (I-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ []) (K-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (sym r5)
    ⨾ ctx (K-gen ∷ []) (I-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (sym r5)
    ⨾ ctx [] (K-gen ∷ K-gen ∷ []) (I-gen ∷ I-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (sym r2)
    ⨾ ctx (I-gen ∷ I-gen ∷ []) (I-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) [] r38
    ⨾ ctx (I-gen ∷ []) (I-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ []) [] r28

  r43 : from-list (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ []) ≈ from-list (S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ [])
  r43 =
    ctx [] (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (I-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (K-gen ∷ []) (sym r34)
    ⨾ ctx [] (I-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (sym r4)
    ⨾ ctx (S-gen ∷ []) (I-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ []) [] r28

  r44 : from-list (I-gen ∷ I-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) ≈ from-list (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ [])
  r44 =
    ctx (I-gen ∷ []) (I-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (K-gen ∷ []) (sym r42)
    ⨾ ctx [] (I-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (sym r5)
    ⨾ ctx (K-gen ∷ []) (I-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ []) [] r28


------------------------------------------------------------------------
-- The equations (X = K S S K iI)

XX : from-list (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) ≈ from-list []
XX =
  ctx (K-gen ∷ S-gen ∷ S-gen ∷ []) (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r5
  ⨾ ctx (K-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (K-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r4
  ⨾ ctx (K-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r4
  ⨾ ctx [] (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r5
  ⨾ ctx [] (I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r20
  ⨾ ctx [] (K-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ []) (S-gen ∷ K-gen ∷ I-gen ∷ []) r40
  ⨾ ctx (S-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ []) r21
  ⨾ ctx [] (S-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) [] (K-gen ∷ K-gen ∷ I-gen ∷ []) r1
  ⨾ ctx (K-gen ∷ []) (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) [] r5
  ⨾ ctx [] (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) (K-gen ∷ []) r5
  ⨾ ctx [] (I-gen ∷ K-gen ∷ K-gen ∷ []) [] [] r8

XSXS : from-list (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) ≈ from-list (I-gen ∷ [])
XSXS =
  ctx (K-gen ∷ S-gen ∷ S-gen ∷ []) (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r5
  ⨾ ctx (K-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r4
  ⨾ ctx (K-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r4
  ⨾ ctx [] (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r5
  ⨾ ctx (I-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r43
  ⨾ ctx (I-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ []) (S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r40
  ⨾ ctx (I-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) [] (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r1
  ⨾ ctx (I-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ S-gen ∷ []) r21
  ⨾ ctx [] (I-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ []) (I-gen ∷ S-gen ∷ []) r22
  ⨾ ctx (S-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ []) r4
  ⨾ ctx (S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ S-gen ∷ []) r4
  ⨾ ctx [] (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ []) r4
  ⨾ ctx (I-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) [] [] r1

XSX⁴ : from-list (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) ≈ from-list []
XSX⁴ =
  ctx (K-gen ∷ S-gen ∷ S-gen ∷ []) (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r5
  ⨾ ctx (K-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r4
  ⨾ ctx (K-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r4
  ⨾ ctx [] (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r5
  ⨾ ctx (I-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r43
  ⨾ ctx (I-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ []) (S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r40
  ⨾ ctx (I-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) [] (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r1
  ⨾ ctx (I-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r21
  ⨾ ctx [] (I-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ []) (I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r22
  ⨾ ctx (S-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r4
  ⨾ ctx (S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r4
  ⨾ ctx [] (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r4
  ⨾ ctx [] (I-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r34
  ⨾ ctx (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r4
  ⨾ ctx (K-gen ∷ S-gen ∷ S-gen ∷ []) (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r5
  ⨾ ctx (K-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r4
  ⨾ ctx (K-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r4
  ⨾ ctx [] (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r5
  ⨾ ctx (I-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (I-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r42
  ⨾ ctx (I-gen ∷ I-gen ∷ S-gen ∷ S-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ []) (S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r40
  ⨾ ctx (I-gen ∷ I-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r21
  ⨾ ctx (I-gen ∷ I-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) [] (S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r1
  ⨾ ctx (I-gen ∷ []) (I-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (S-gen ∷ S-gen ∷ []) (I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r17
  ⨾ ctx (I-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r4
  ⨾ ctx (I-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r4
  ⨾ ctx [] (I-gen ∷ I-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ []) (I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r44
  ⨾ ctx (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r4
  ⨾ ctx (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r4
  ⨾ ctx (K-gen ∷ S-gen ∷ S-gen ∷ []) (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r5
  ⨾ ctx (K-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r4
  ⨾ ctx (K-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r4
  ⨾ ctx [] (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r5
  ⨾ ctx (I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r40
  ⨾ ctx (I-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r40
  ⨾ ctx [] (I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r18
  ⨾ ctx (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ []) (K-gen ∷ K-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ K-gen ∷ []) (S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r10
  ⨾ ctx (S-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ []) (K-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r40
  ⨾ ctx (S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ []) (K-gen ∷ K-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r10
  ⨾ ctx (S-gen ∷ S-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (K-gen ∷ K-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r21
  ⨾ ctx [] (S-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) [] (S-gen ∷ K-gen ∷ K-gen ∷ K-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r1
  ⨾ ctx (S-gen ∷ []) (K-gen ∷ K-gen ∷ K-gen ∷ K-gen ∷ []) (I-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r6
  ⨾ ctx [] (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (I-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r4
  ⨾ ctx (I-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r4
  ⨾ ctx (I-gen ∷ I-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r4
  ⨾ ctx [] (I-gen ∷ I-gen ∷ I-gen ∷ []) (K-gen ∷ K-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r2
  ⨾ ctx [] (K-gen ∷ K-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ K-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r10
  ⨾ ctx (S-gen ∷ K-gen ∷ []) (K-gen ∷ K-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ K-gen ∷ []) (S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r10
  ⨾ ctx (S-gen ∷ K-gen ∷ S-gen ∷ []) (K-gen ∷ K-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r10
  ⨾ ctx (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r5
  ⨾ ctx (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r5
  ⨾ ctx (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ []) (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) (K-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r5
  ⨾ ctx (S-gen ∷ K-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (K-gen ∷ K-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r4
  ⨾ ctx (S-gen ∷ K-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ K-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r4
  ⨾ ctx (S-gen ∷ []) (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r5
  ⨾ ctx [] (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r4
  ⨾ ctx [] (I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r24
  ⨾ ctx [] (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r35
  ⨾ ctx [] (I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) r20
  ⨾ ctx [] (K-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ []) (S-gen ∷ K-gen ∷ I-gen ∷ []) r40
  ⨾ ctx (S-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ []) r21
  ⨾ ctx [] (S-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) [] (K-gen ∷ K-gen ∷ I-gen ∷ []) r1
  ⨾ ctx (K-gen ∷ []) (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) [] r5
  ⨾ ctx [] (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) (K-gen ∷ []) r5
  ⨾ ctx [] (I-gen ∷ K-gen ∷ K-gen ∷ []) [] [] r8

XSX-S : from-list (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) ≈ from-list (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ [])
XSX-S =
  ctx (K-gen ∷ S-gen ∷ S-gen ∷ []) (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r5
  ⨾ ctx (K-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r4
  ⨾ ctx (K-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r4
  ⨾ ctx [] (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r5
  ⨾ ctx (I-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r43
  ⨾ ctx (I-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ []) (S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r40
  ⨾ ctx (I-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) [] (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r1
  ⨾ ctx (I-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ S-gen ∷ []) r21
  ⨾ ctx [] (I-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ []) (I-gen ∷ S-gen ∷ []) r22
  ⨾ ctx (S-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ []) r4
  ⨾ ctx (S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ S-gen ∷ []) r4
  ⨾ ctx [] (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ []) r4
  ⨾ ctx (I-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) [] [] r1
  ⨾ ctx [] [] (I-gen ∷ K-gen ∷ K-gen ∷ []) (I-gen ∷ []) (sym r8)
  ⨾ ctx (I-gen ∷ []) [] (S-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) (K-gen ∷ K-gen ∷ I-gen ∷ []) (sym r1)
  ⨾ ctx (I-gen ∷ S-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (K-gen ∷ I-gen ∷ []) (sym r21)
  ⨾ ctx (I-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ I-gen ∷ []) (sym r40)
  ⨾ ctx (I-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ []) (I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) (sym r20)
  ⨾ ctx (I-gen ∷ []) (I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) (sym r35)
  ⨾ ctx [] (I-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) (sym r4)
  ⨾ ctx (S-gen ∷ []) (I-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) (sym r5)
  ⨾ ctx (S-gen ∷ K-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) (sym r4)
  ⨾ ctx (S-gen ∷ K-gen ∷ S-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) (sym r4)
  ⨾ ctx (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ []) (I-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) (sym r5)

S-X : from-list (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) ≈ from-list (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ [])
S-X =
  ctx (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ []) (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) [] r5
  ⨾ ctx (S-gen ∷ K-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (K-gen ∷ []) r4
  ⨾ ctx (S-gen ∷ K-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ []) r4
  ⨾ ctx (S-gen ∷ []) (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ []) r5
  ⨾ ctx [] (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) r4
  ⨾ ctx [] (I-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (sym r4)
  ⨾ ctx (S-gen ∷ []) (I-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ []) (sym r5)
  ⨾ ctx (S-gen ∷ K-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (S-gen ∷ K-gen ∷ []) (sym r4)
  ⨾ ctx (S-gen ∷ K-gen ∷ S-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (K-gen ∷ []) (sym r4)
  ⨾ ctx (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ []) (I-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ []) [] (sym r5)
  ⨾ ctx [] [] (I-gen ∷ K-gen ∷ K-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) (sym r8)
  ⨾ ctx [] (I-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) (sym r5)
  ⨾ ctx (K-gen ∷ []) (I-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) (sym r5)
  ⨾ ctx [] [] (S-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) (K-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) (sym r1)
  ⨾ ctx (S-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) (sym r21)
  ⨾ ctx [] (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) (sym r40)
  ⨾ ctx [] (K-gen ∷ S-gen ∷ S-gen ∷ []) (I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) (sym r20)
  ⨾ ctx [] (I-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) (sym r5)
  ⨾ ctx (K-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (S-gen ∷ K-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) (sym r4)
  ⨾ ctx (K-gen ∷ S-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (K-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) (sym r4)
  ⨾ ctx (K-gen ∷ S-gen ∷ S-gen ∷ []) (I-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ []) (sym r5)

K-Z : from-list (K-gen ∷ S-gen ∷ S-gen ∷ []) ≈ from-list (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ K-gen ∷ [])
K-Z =
  ctx [] (K-gen ∷ S-gen ∷ S-gen ∷ []) (I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) [] (sym r20)
  ⨾ ctx [] (I-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (sym r5)
  ⨾ ctx (K-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (S-gen ∷ K-gen ∷ K-gen ∷ []) (sym r4)
  ⨾ ctx (K-gen ∷ S-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (K-gen ∷ K-gen ∷ []) (sym r4)
  ⨾ ctx (K-gen ∷ S-gen ∷ S-gen ∷ []) (I-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ []) (K-gen ∷ []) (sym r5)

K-S³ : from-list (K-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) ≈ from-list (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ [])
K-S³ =
  ctx [] (K-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ []) [] r40

K-XSXS : from-list (K-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) ≈ from-list (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ [])
K-XSXS =
  ctx [] (K-gen ∷ K-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ K-gen ∷ []) (S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r10
  ⨾ ctx (S-gen ∷ []) (K-gen ∷ K-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r10
  ⨾ ctx (S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r5
  ⨾ ctx (S-gen ∷ S-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r5
  ⨾ ctx (S-gen ∷ S-gen ∷ []) (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) (K-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r5
  ⨾ ctx (S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (K-gen ∷ K-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r4
  ⨾ ctx [] (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ K-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r4
  ⨾ ctx [] (I-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (S-gen ∷ S-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r17
  ⨾ ctx (S-gen ∷ S-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r21
  ⨾ ctx [] (S-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) [] (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r1
  ⨾ ctx (S-gen ∷ K-gen ∷ S-gen ∷ []) (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) (S-gen ∷ []) r5
  ⨾ ctx (S-gen ∷ K-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (K-gen ∷ S-gen ∷ []) r4
  ⨾ ctx (S-gen ∷ []) (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ []) r5
  ⨾ ctx [] (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) r4
  ⨾ ctx (I-gen ∷ S-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) [] r21
  ⨾ ctx (I-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) [] (K-gen ∷ []) r1
  ⨾ ctx (I-gen ∷ []) [] (S-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) (K-gen ∷ []) (sym r1)
  ⨾ ctx [] (I-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (sym r4)
  ⨾ ctx (S-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ []) (sym r4)
  ⨾ ctx (S-gen ∷ S-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (S-gen ∷ K-gen ∷ []) (sym r4)
  ⨾ ctx [] (S-gen ∷ S-gen ∷ S-gen ∷ []) (I-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (I-gen ∷ S-gen ∷ K-gen ∷ []) (sym r22)
  ⨾ ctx (I-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ []) (sym r21)
  ⨾ ctx (I-gen ∷ []) [] (S-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ []) (sym r1)
  ⨾ ctx (I-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ []) (sym r40)
  ⨾ ctx (I-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ []) (sym r43)
  ⨾ ctx [] (I-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ []) (sym r5)
  ⨾ ctx (K-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ []) (sym r4)
  ⨾ ctx (K-gen ∷ S-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ []) (sym r4)
  ⨾ ctx (K-gen ∷ S-gen ∷ S-gen ∷ []) (I-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ []) (sym r5)

K²XSXS : from-list (K-gen ∷ K-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) ≈ from-list []
K²XSXS =
  ctx (K-gen ∷ []) (K-gen ∷ K-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ K-gen ∷ []) (S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r10
  ⨾ ctx (K-gen ∷ S-gen ∷ []) (K-gen ∷ K-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r10
  ⨾ ctx (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r5
  ⨾ ctx (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r5
  ⨾ ctx (K-gen ∷ S-gen ∷ S-gen ∷ []) (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) (K-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r5
  ⨾ ctx (K-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (K-gen ∷ K-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r4
  ⨾ ctx (K-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ K-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r4
  ⨾ ctx [] (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r5
  ⨾ ctx [] (I-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ []) (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r20
  ⨾ ctx [] (K-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ S-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r43
  ⨾ ctx (S-gen ∷ S-gen ∷ S-gen ∷ []) (K-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ []) (S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r40
  ⨾ ctx [] (S-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) [] (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ K-gen ∷ I-gen ∷ S-gen ∷ []) r1
  ⨾ ctx [] (K-gen ∷ S-gen ∷ K-gen ∷ S-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ S-gen ∷ []) r21
  ⨾ ctx (S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ []) (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) (S-gen ∷ []) r5
  ⨾ ctx (S-gen ∷ S-gen ∷ S-gen ∷ []) (K-gen ∷ I-gen ∷ []) (I-gen ∷ K-gen ∷ []) (K-gen ∷ S-gen ∷ []) r5
  ⨾ ctx (S-gen ∷ S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (K-gen ∷ K-gen ∷ S-gen ∷ []) r4
  ⨾ ctx (S-gen ∷ []) (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ K-gen ∷ K-gen ∷ S-gen ∷ []) r4
  ⨾ ctx [] (S-gen ∷ I-gen ∷ []) (I-gen ∷ S-gen ∷ []) (S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ S-gen ∷ []) r4
  ⨾ ctx [] (I-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ K-gen ∷ K-gen ∷ []) (S-gen ∷ S-gen ∷ S-gen ∷ []) (S-gen ∷ []) r22
  ⨾ ctx [] (S-gen ∷ S-gen ∷ S-gen ∷ S-gen ∷ []) [] [] r1

K⁸ : from-list (K-gen ∷ K-gen ∷ K-gen ∷ K-gen ∷ K-gen ∷ K-gen ∷ K-gen ∷ K-gen ∷ []) ≈ from-list []
K⁸ =
  ctx [] (K-gen ∷ K-gen ∷ K-gen ∷ K-gen ∷ []) (I-gen ∷ I-gen ∷ []) (K-gen ∷ K-gen ∷ K-gen ∷ K-gen ∷ []) r6
  ⨾ ctx (I-gen ∷ []) (I-gen ∷ K-gen ∷ K-gen ∷ []) [] (K-gen ∷ K-gen ∷ []) r8
  ⨾ ctx [] (I-gen ∷ K-gen ∷ K-gen ∷ []) [] [] r8

