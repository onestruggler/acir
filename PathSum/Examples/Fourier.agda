------------------------------------------------------------------------
-- Presentations of groups
--
-- Section 2.2: the Fourier expansion of a phase is not unique modulo
-- integers
--
-- Section 2.2 of Amy's QPL 2018 paper: "the Fourier expansion is not
-- necessarily unique modulo integer multiples".  A witness at the
-- examples' precision M₀ = 0 (eighths: ¼ is 2, ½ is 4), with
-- PathSum.Fourier's expansions.
--
-- The controlled-Z phase ½ x1x2 (czᴾ) has the two expansions
--
--    E₊ = ¼ x1 + ¼ x2 − ¼ (x1 ⊕ x2)    and    E₋ = −¼ x1 − ¼ x2 + ¼ (x1 ⊕ x2):
--
-- the first is ½ x1x2 exactly, since x1 + x2 − (x1 ⊕ x2) = 2 x1x2,
-- and the second is −½ x1x2, which differs from it by the integer
-- x1x2.  Both represent the phase modulo 1 at every point, with no
-- raised precision (cz-expansions), yet their coefficients on x1 are ¼
-- and −¼ = ¾, which differ modulo 1 (expansions-differ).  So the
-- Fourier expansion of a phase function modulo 1 is not unique
-- (fourier-not-unique), whereas its multilinear form is
-- (PathSum.Fourier.phase-unique): the coefficient ½ of x1x2 is the
-- only one modulo 1.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Examples.Fourier where

open import Data.Fin.Base using (zero; suc)
open import Data.Fin.Subset using (inside; outside)
open import Data.Integer.Base using (0ℤ; +_; -_; _-_)
open import Data.Integer.Divisibility.Signed using (_∣_; _∣?_)
open import Data.List.Base using ([]; _∷_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using ([]; _∷_)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Order 3 using (pow)
open import PathSum.Polynomial using (Poly; Mon; _·ᴾ_)
open import PathSum.Polynomial.Product using (monoᴾ)

import PathSum.Fourier as F


------------------------------------------------------------------------
-- The phase and its two expansions

-- The parity sets x1, x2 and x1 ⊕ x2 (as monomials: their variables).

X₁ X₂ X₁₂ : Mon 2 0
X₁  = inside  ∷ outside ∷ [] , []
X₂  = outside ∷ inside  ∷ [] , []
X₁₂ = inside  ∷ inside  ∷ [] , []

-- The controlled-Z phase ½ x1x2.

czᴾ : Poly 2 0
czᴾ = (+ 4) ·ᴾ monoᴾ X₁₂

-- ¼ x1 + ¼ x2 − ¼ (x1 ⊕ x2), and its negative.

E₊ E₋ : F.Expansion 0 2 0
E₊ = 0ℤ , ((+ 2 , X₁) ∷ (+ 2 , X₂) ∷ (- (+ 2) , X₁₂) ∷ [])
E₋ = 0ℤ , ((- (+ 2) , X₁) ∷ (- (+ 2) , X₂) ∷ (+ 2 , X₁₂) ∷ [])


------------------------------------------------------------------------
-- Both represent it modulo 1, with different coefficients

-- At every point, with numerators over 2^3 (no raised precision).

cz-expansions : F.FourierOf 0 0 E₊ czᴾ × F.FourierOf 0 0 E₋ czᴾ
cz-expansions = toWitness {a? = F.fourierOf? 0 0 E₊ czᴾ} tt ,
                toWitness {a? = F.fourierOf? 0 0 E₋ czᴾ} tt

-- Their coefficients on x1, ¼ and −¼, differ modulo 1.

expansions-differ : ¬ (pow 3 ∣ (F.coefᶠ 0 E₊ X₁ - F.coefᶠ 0 E₋ X₁))
expansions-differ =
  toWitnessFalse {a? = pow 3 ∣? (F.coefᶠ 0 E₊ X₁ - F.coefᶠ 0 E₋ X₁)} tt

fourier-not-unique :
  F.FourierOf 0 0 E₊ czᴾ × F.FourierOf 0 0 E₋ czᴾ ×
  ¬ (pow 3 ∣ (F.coefᶠ 0 E₊ X₁ - F.coefᶠ 0 E₋ X₁))
fourier-not-unique =
  proj₁ cz-expansions , proj₂ cz-expansions , expansions-differ
