------------------------------------------------------------------------
-- Presentations of groups
--
-- The inverse of a Clifford circuit (Amy, QPL 2018, sections 2.2
-- and 3)
--
-- Section 3 checks a circuit C against a specification ξ by asking
-- whether the miter ⟦ C† ⟧ ∘ ξ is the identity, and section 2.2
-- builds the interpretation of a circuit from the path-sums of its
-- gates "and their inverses".  This module is the syntax of that
-- inverse: C† runs the gates of C last to first, each replaced by its
-- inverse.  Hadamard and CZ are their own inverses.  The gate set
-- {H , S , CZ} has no S†, so S³ stands in for it: its phase is ¾ x
-- where the paper's ⟦ S† ⟧ would have -¼ x, and the two agree modulo
-- 1, which is all a phase is read modulo.  S³ has no Hadamard, so C†
-- has the normalisation of C.
--
-- Only the syntax is here.  That C† inverts C on both sides is
-- PathSum.Miter's †-cancelʳ and †-cancelˡ, proved on columns gate by
-- gate; that it is the conjugate transpose -- the adjoint proper --
-- would need conjugation in Z[ζ], and is not stated.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Adjoint (M : ℕ) where

open import Data.List.Base using ([]; _∷_; _++_)
open import Data.Nat.Base using (suc; _+_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

open import PathSum.Circuit M using (Gate; H; S; CZ; Circuit; norm)

import Data.Nat.Properties as ℕ

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- The inverse of a gate, and of a circuit

-- S† is spelled S S S.

inv : Gate n → Circuit n
inv (H w)    = H w ∷ []
inv (S w)    = S w ∷ S w ∷ S w ∷ []
inv (CZ w v) = CZ w v ∷ []

-- The gates of C† are those of C, inverted, in the opposite order.
-- The fixity makes C₁ ++ C₂ † the circuit C₁ followed by C₂†, and
-- lets C † † parse.

infixl 8 _†

_† : Circuit n → Circuit n
[]      † = []
(g ∷ C) † = C † ++ inv g


------------------------------------------------------------------------
-- Normalisation

-- The normalisation counts Hadamards, so it adds up along a
-- concatenation, and inverting a gate or a circuit leaves it alone.

norm-++ : (C D : Circuit n) → norm (C ++ D) ≡ norm C + norm D
norm-++ []           D = refl
norm-++ (H _ ∷ C)    D = cong suc (norm-++ C D)
norm-++ (S _ ∷ C)    D = norm-++ C D
norm-++ (CZ _ _ ∷ C) D = norm-++ C D

norm-inv : (g : Gate n) → norm (inv g) ≡ norm (g ∷ [])
norm-inv (H _)    = refl
norm-inv (S _)    = refl
norm-inv (CZ _ _) = refl

norm-† : (C : Circuit n) → norm (C †) ≡ norm C
norm-† []      = refl
norm-† (g ∷ C) =
  trans (norm-++ (C †) (inv g))
    (trans (cong₂ _+_ (norm-† C) (norm-inv g))
      (trans (ℕ.+-comm (norm C) (norm (g ∷ [])))
             (sym (norm-++ (g ∷ []) C))))
