------------------------------------------------------------------------
-- Presentations of groups
--
-- Closed execution checks of the normalizer at p = 3, 5, 7.
-- Every equality below is checked by reduction (refl), not by applying
-- a presentation axiom or the semantic completeness theorem.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Symplectic.Normalization.Computations where

open import Data.Nat.Primality using (prime?)
open import Relation.Nullary.Decidable using (from-yes)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Word.Base using (ε ; _^_ ; _•_)

import Examples.Groups.Symplectic.Normalization as Norm
import Examples.Groups.Symplectic.Syntactics as Syn

module At3 where

  module N = Norm 1 (from-yes (prime? 3))
  module S = Syn 1 (from-yes (prime? 3))
  open S.Symplectic using (S ; H ; CZ)

  phase-order : N.nf-of (S {0} ^ 3) ≡ N.nf-of ε
  phase-order = refl

  fourier-order : N.nf-of (H {0} ^ 4) ≡ N.nf-of ε
  fourier-order = refl

  controlled-phase-order : N.nf-of (CZ {0} ^ 3) ≡ N.nf-of ε
  controlled-phase-order = refl

module At5 where

  module N = Norm 3 (from-yes (prime? 5))
  module S = Syn 3 (from-yes (prime? 5))
  open S.Symplectic using (S ; H ; CZ)

  phase-order : N.nf-of (S {0} ^ 5) ≡ N.nf-of ε
  phase-order = refl

  fourier-order : N.nf-of (H {0} ^ 4) ≡ N.nf-of ε
  fourier-order = refl

  controlled-phase-order : N.nf-of (CZ {0} ^ 5) ≡ N.nf-of ε
  controlled-phase-order = refl

module At7 where

  module N = Norm 5 (from-yes (prime? 7))
  module S = Syn 5 (from-yes (prime? 7))
  open S.Symplectic using (S ; H ; CZ)

  phase-order : N.nf-of (S {0} ^ 7) ≡ N.nf-of ε
  phase-order = refl

  fourier-order : N.nf-of (H {0} ^ 4) ≡ N.nf-of ε
  fourier-order = refl

  controlled-phase-order : N.nf-of (CZ {0} ^ 7) ≡ N.nf-of ε
  controlled-phase-order = refl
