------------------------------------------------------------------------
-- Presentations of groups
--
-- The postulated normalizer for the symplectic presentation
--
-- Normalization.Uniqueness proves that the normal-form section is
-- injective for the symplectic semantics, and does so outright: it is
-- --safe and postulate-free.  The other half of a NormalForm witness
-- is the normalizer itself — a map Circuit n → NF n retracting the
-- section — and that is still open.  It lives here, on its own, so
-- that the file is the only non---safe one on this route and it is
-- plain which results depend on it.
--
-- Sources for nf-t would be the Reidemeister–Schreier tower of
-- Normalization.agda (which needs srel-wd per width) or a direct
-- rewriting normalizer.  Nothing about uniqueness depends on it.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Normalizer
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

import Normalization.NormalForm.Propositional as NFBase
import Presentation.Base as PB
open NFBase using (NormalForm)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic
open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

------------------------------------------------------------------------
-- The normalizer

-- nf-t sends a circuit to its normal form, nf-t-cong makes that
-- respect the presentation's congruence, and retract-t says the
-- section undoes it.

postulate
  nf-t      : ∀ {n} → Circuit n → NF n
  nf-t-cong : ∀ {n} {w v : Circuit n} →
              PB._≈_ (n QRel,_===_) w v → nf-t w ≡ nf-t v
  retract-t : ∀ {n} {w : Circuit n} → PB._≈_ (n QRel,_===_) [ nf-t w ] w

-- Packaged as a NormalForm witness, with [_] as its section.
nfp'-t : ∀ n → NormalForm (n QRel,_===_) (NF n)
nfp'-t n = record
  { rightInverse = record
      { to        = nf-t
      ; from      = [_]
      ; to-cong   = nf-t-cong
      ; from-cong = λ { Eq.refl → refl }
      ; inverseʳ  = λ { Eq.refl → retract-t }
      }
  }
  where open PB (n QRel,_===_)
