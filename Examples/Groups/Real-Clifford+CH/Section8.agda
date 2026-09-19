------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness on n ≥ 3 qubits (Clément, Section 8), assembled from
-- the encoding, the decoding and the theory of P
--
-- The back-and-forth argument of BackAndForth, instantiated with the
-- generators P (Proposition 4.6) and their theory (Figure 8), the
-- encoding of Definition 8.2 and the decoding of Definition 8.3.  Its
-- four inputs are the paper's Theorem 4.10 (completeness of Figure 8,
-- Appendix A), that the encoding preserves the semantics (Definition
-- 8.2), Lemma 8.8 (the decoding respects Figure 8, Appendix E.5) and
-- Lemma 8.7 (the decoding inverts the encoding, Appendix E.4).  They
-- are the module's parameters, stated here about these definitions;
-- the second is proved at every width in EncodingSemantics (which
-- Completeness passes in), and Checks8 decides the soundness half of
-- the first on three qubits.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Section8 where

open import Data.Nat using (ℕ)
open import Word.Base using (Word ; [_]ʷ ; _ʷ)

open import Notations using (₃₊)

import Presentation.Base as PB

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8
open import Examples.Groups.Real-Clifford+CH.Encoding using (e)
open import Examples.Groups.Real-Clifford+CH.Decoding using (d)

import Examples.Groups.Real-Clifford+CH.BackAndForth as BackAndForth

module _ (m : ℕ) where
  private
    n : ℕ
    n = ₃₊ m

  module BF = BackAndForth n (m P,_===_) ⟦_⟧ᴾ
  open BF using (⟦_⟧Y) public

  open PB (m P,_===_) using () renaming (_≈_ to _≈ᴾ_)

  -- The hypotheses of Section 8, as statements about these definitions.
  Theorem-4-10 : Set
  Theorem-4-10 = ∀ {u t : Word (GenP n)} → ⟦ u ⟧Y ~ ⟦ t ⟧Y → u ≈ᴾ t

  E-sem : Set
  E-sem = ∀ g → ⟦ e g ⟧Y ~ ⟦ [ g ]ʷ ⟧

  Lemma-8-8 : Set
  Lemma-8-8 = ∀ {u t} → m P, u === t → n ⊢ (d ʷ) u ≈ (d ʷ) t

  Lemma-8-7 : Set
  Lemma-8-7 = ∀ g → n ⊢ [ g ]ʷ ≈ (d ʷ) (e g)

  module Complete (theorem-4-10 : Theorem-4-10) (e-sem : E-sem)
                  (lemma-8-8 : Lemma-8-8) (lemma-8-7 : Lemma-8-7) where
    open BF.Complete theorem-4-10 e e-sem d lemma-8-8 lemma-8-7 public
      using (complete)
