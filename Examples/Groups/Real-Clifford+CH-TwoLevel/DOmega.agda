------------------------------------------------------------------------
-- Presentations of groups
--
-- Oₙ(𝔻[√2]) as a subgroup of Uₙ(𝔻[ω]), and Hadamard-Pi's
-- presentation read there
--
-- 𝔻[√2] = ℤ[1/√2] is a subring of 𝔻[ω] = ℤ[1/√2, i]: x + y√2 is
-- -yω³ + yω + x, since √2 = ω - ω³ (EucDomain's rootTwo→ω), an
-- injective ring homomorphism that commutes with conjugation (the
-- identity on 𝔻[√2]).  So Oₙ(𝔻[√2]) is a subgroup of Uₙ(𝔻[ω])
-- (Embed), and Figure 6, given the case of the Main Lemma that
-- Hadamard-Pi's proof misses (Hard), is a sub-presentation of
-- Uₙ(𝔻[ω]) (presentation-given).  Real-Clifford+CH-TwoLevel-Clement,
-- which proves that case, reads the theorem in Uₙ(𝔻[ω]) through Embed,
-- as do Real-Clifford+CH (Clément's circuits) and, through Emb, the
-- scaled dyadic groups of CCX+HH-TwoLevel.Scaled.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH-TwoLevel.DOmega where

open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

import Quantum.Synthesis.Ring as QR
import Quantum.Synthesis.Ring.Properties.Embedding as E

open import Presentation.Definitions using (_IsSubPresentationOf_)

open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics using (_===_)
import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring as R
import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics as S
import Examples.Groups.Real-Clifford+CH-TwoLevel.MainLemma as ML
import Examples.Groups.Real-Clifford+CH-TwoLevel.Presentation as P
import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring as Ω
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics using (U)
import Examples.Groups.Clifford+T-2qubit-TwoLevel.Subring as Subring

------------------------------------------------------------------------
-- 𝔻[√2] in 𝔻[ω], with the (opaque) operations of both

ι : R.D → Ω.D
ι = E.rootTwo→ω ⦃ QR.RingDyadic ⦄

opaque
  unfolding R._+ᴰ_ R._*ᴰ_ R.adjᴰ Ω._+ᴰ_ Ω._*ᴰ_ Ω.adjᴰ

  ι-+ : ∀ x y → ι (x R.DR.+ y) ≡ ι x Ω.DR.+ ι y
  ι-+ = E.At-𝔻.rootTwo→ω-+

  ι-* : ∀ x y → ι (x R.DR.* y) ≡ ι x Ω.DR.* ι y
  ι-* = E.At-𝔻.rootTwo→ω-*

  ι-adj : ∀ x → ι (R.adjᴰ x) ≡ Ω.adjᴰ (ι x)
  ι-adj = E.At-𝔻.rootTwo→ω-adj

ι-0 : ι R.DR.0# ≡ Ω.DR.0#
ι-0 = E.At-𝔻.rootTwo→ω-0

ι-1 : ι R.DR.1# ≡ Ω.DR.1#
ι-1 = E.At-𝔻.rootTwo→ω-1

-- Matrices over 𝔻[√2] as matrices over 𝔻[ω].
module Emb = Subring {A = R.D} ⦃ R.RingD ⦄ ⦃ R.AdjointD ⦄ R.isCommutativeRing-D R.adj-D
               ι ι-+ ι-* ι-0 ι-1 ι-adj (E.rootTwo→ω-injective ⦃ QR.RingDyadic ⦄)

------------------------------------------------------------------------
-- Oₙ(𝔻[√2]) in Uₙ(𝔻[ω])

module Embed (n : ℕ) =
  Emb.Group-Embedding (S.O n) n proj₁ proj₂ (λ e → e) (λ e → e) (λ _ _ → refl) refl

------------------------------------------------------------------------
-- Hadamard-Pi's proof, read in Uₙ(𝔻[ω])

presentation-given : ∀ {n} → ML.Hard {n} → (_===_ {n}) IsSubPresentationOf U n
presentation-given {n} hard = Embed.along-presentation n (P.presentation {n} hard)
