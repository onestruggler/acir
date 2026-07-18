------------------------------------------------------------------------
-- Presentations of groups
--
-- A group presentation of the Pauli group Pauli n = (ℤ/pℤ × ℤ/pℤ)ⁿ.
--
-- Built entirely from the three construction properties:
--   * the cyclic presentation of ℤ/pℤ  (Examples.Groups.Cyclic.Presentation),
--   * the binary direct product        (Construct.Properties.DirectProduct),
--   * the n-fold direct product        (Construct.Properties.NDirectProduct).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; suc ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Pauli.Presentation (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Algebra.Bundles using (Group)
open import Level using (0ℓ)

open import Notations
open import Presentation.Definitions using (_IsPresentationOf_)
open import Presentation.Construct.Base using (_⋄_⋄_ ; CommRel ; _⊕^_)
import Presentation.Construct.Properties.DirectProduct as DP
import Presentation.Construct.Properties.NDirectProduct as NDP

open import Examples.Groups.Cyclic.Normalization using (_Cn,_===_)
open import Examples.Groups.Cyclic.Semantics using (Cn-group)
import Examples.Groups.Cyclic.Presentation as CyP

private
  -- The modulus is ₚ = 2+ p-2 = ₁₊ m.
  m : ℕ
  m = suc p-2

------------------------------------------------------------------------
-- ℤ/pℤ, presented as a cyclic group of order ₚ

Cₚ = ₁₊ m Cn,_===_

Gₚ : Group 0ℓ 0ℓ
Gₚ = Cn-group (₁₊ m)

ℤ/p-pres : Cₚ IsPresentationOf Gₚ
ℤ/p-pres = CyP.presentation {m}

------------------------------------------------------------------------
-- ℤ/pℤ × ℤ/pℤ, presented by the binary direct product

private module DPₚ = DP.Presentation Cₚ Cₚ Gₚ Gₚ ℤ/p-pres ℤ/p-pres

Γ-H = Cₚ ⋄ Cₚ ⋄ CommRel

H-group : Group 0ℓ 0ℓ
H-group = DPₚ.dp

H-pres : Γ-H IsPresentationOf H-group
H-pres = DPₚ.dpres

------------------------------------------------------------------------
-- Pauli n = (ℤ/pℤ × ℤ/pℤ)ⁿ, presented by the n-fold direct product

private module NDₚ = NDP.Presentation Γ-H H-group H-pres

-- The Pauli group of n qupits.
Pauli-group : ℕ → Group 0ℓ 0ℓ
Pauli-group = NDₚ.⊗-group

-- Γ-H ⊕^ n presents it.
Pauli-presentation : (n : ℕ) → (Γ-H ⊕^ n) IsPresentationOf (Pauli-group n)
Pauli-presentation = NDₚ.presentation
