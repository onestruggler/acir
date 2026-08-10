------------------------------------------------------------------------
-- Presentations of groups
--
-- Normal-form properties for N-fold direct products of group
-- presentations
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Word.Base using (WRel)

module Presentation.Construct.Properties.NDirectProduct
  {A : Set}
  (Γ : WRel A)
  where

open import Algebra.Bundles using (Group)
import Algebra.Construct.DirectProduct as ADP
open import Data.Nat using (ℕ ; zero)
open import Data.Product using (_×_)
open import Data.Unit using (⊤)
open import Level using (0ℓ)

open import Normalization.NormalForm.Propositional
  using (NormalForm ; NormalFormInjective)
open import Notations using (₁₊ ; ₂₊)
open import Presentation.Construct.Base using (_⊕^_)
open import Presentation.Definitions using (_IsPresentationOf_)
import Presentation.Construct.Properties.DirectProduct as DP
import Examples.Groups.Trivial as Trivial

------------------------------------------------------------------------
-- Normal forms for n-fold direct products
--
-- Both witnesses are lifted by induction on n: at n = 0 the product
-- is the trivial group, at n = 1 it is Γ itself, and at n ≥ 2 the
-- binary direct-product lifting is applied to Γ and the (n - 1)-fold
-- product.

-- The carrier of the n-fold product normal form: ⊤ at n = 0, the
-- factor's carrier NF at n = 1, and NF × (previous carrier) beyond.
⊗-carrier : ℕ → Set → Set
⊗-carrier zero      NF = ⊤
⊗-carrier (₁₊ zero) NF = NF
⊗-carrier (₂₊ n)    NF = NF × ⊗-carrier (₁₊ n) NF

-- A normal-form witness for Γ lifts to the n-fold direct product
-- Γ ⊕^ n.
nfp : (n : ℕ) {NF : Set} → NormalFormInjective Γ NF
    → NormalFormInjective (Γ ⊕^ n) (⊗-carrier n NF)
nfp zero nfΓ = Trivial.Empty.nfp
nfp (₁₊ zero) nfΓ = nfΓ
nfp (₂₊ n) nfΓ = DP.NFP.nfp Γ (Γ ⊕^ ₁₊ n) nfΓ (nfp (₁₊ n) nfΓ)

-- Like nfp, but for witnesses that also carry a section inv-nf of
-- the normal-form function; the section is lifted the same way.
nfp' : (n : ℕ) {NF : Set} → NormalForm Γ NF → NormalForm (Γ ⊕^ n) (⊗-carrier n NF)
nfp' zero nfΓ = Trivial.Empty.nfp'
nfp' (₁₊ zero) nfΓ = nfΓ
nfp' (₂₊ n) nfΓ = DP.NFP'.nfp' Γ (Γ ⊕^ ₁₊ n) nfΓ (nfp' (₁₊ n) nfΓ)

------------------------------------------------------------------------
-- Presentations for n-fold direct products
--
-- A group presentation of Γ lifts to a group presentation of the n-fold
-- direct product Γ ⊕^ n, by the same induction: at n = 0 the trivial
-- group, at n = 1 the given presentation, and at n ≥ 2 the binary
-- direct-product presentation applied to Γ and the (n-1)-fold product.

module Presentation
  (G : Group 0ℓ 0ℓ)
  (p : Γ IsPresentationOf G)
  where

  -- The n-fold direct product of G: the trivial group at n = 0, G at
  -- n = 1, and G × (previous power) beyond.
  ⊗-group : ℕ → Group 0ℓ 0ℓ
  ⊗-group zero      = Trivial.Empty.Presentation.gp
  ⊗-group (₁₊ zero) = G
  ⊗-group (₂₊ n)    = ADP.group G (⊗-group (₁₊ n))

  -- Γ ⊕^ n presents the n-fold direct product ⊗-group n.
  presentation : (n : ℕ) → (Γ ⊕^ n) IsPresentationOf (⊗-group n)
  presentation zero      = Trivial.Empty.Presentation.presentation
  presentation (₁₊ zero) = p
  presentation (₂₊ n)    =
    DP.Presentation.dpres Γ (Γ ⊕^ ₁₊ n) G (⊗-group (₁₊ n)) p (presentation (₁₊ n))
