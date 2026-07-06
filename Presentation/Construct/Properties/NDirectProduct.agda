------------------------------------------------------------------------
-- Presentations of groups
--
-- Normal-form properties for N-fold direct products of group
-- presentations
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Word.Base using (WRel)

module Presentation.Construct.Properties.NDirectProduct
  {A : Set}
  (Γ : WRel A)
  where

open import Data.Nat using (ℕ ; zero)

open import Normalization.Base
  using (NormalForm ; NormalFormWithoutInverse)
open import Notations using (₁₊ ; ₂₊)
open import Presentation.Construct.Base using (_⊕^_)
import Presentation.Construct.Properties.DirectProduct as DP
import Presentation.Groups.Trivial as Trivial

------------------------------------------------------------------------
-- Normal forms for n-fold direct products
--
-- Both witnesses are lifted by induction on n: at n = 0 the product
-- is the trivial group, at n = 1 it is Γ itself, and at n ≥ 2 the
-- binary direct-product lifting is applied to Γ and the (n - 1)-fold
-- product.

-- A normal-form witness for Γ lifts to the n-fold direct product
-- Γ ⊕^ n.
nfp : (n : ℕ) → NormalFormWithoutInverse Γ
    → NormalFormWithoutInverse (Γ ⊕^ n)
nfp zero nfΓ = Trivial.P1.nfp
nfp (₁₊ zero) nfΓ = nfΓ
nfp (₂₊ n) nfΓ = DP.NFP.nfp Γ (Γ ⊕^ ₁₊ n) nfΓ (nfp (₁₊ n) nfΓ)

-- Like nfp, but for witnesses that also carry a section inv-nf of
-- the normal-form function; the section is lifted the same way.
nfp' : (n : ℕ) → NormalForm Γ → NormalForm (Γ ⊕^ n)
nfp' zero nfΓ = Trivial.P1.nfp'
nfp' (₁₊ zero) nfΓ = nfΓ
nfp' (₂₊ n) nfΓ = DP.NFP'.nfp' Γ (Γ ⊕^ ₁₊ n) nfΓ (nfp' (₁₊ n) nfΓ)
