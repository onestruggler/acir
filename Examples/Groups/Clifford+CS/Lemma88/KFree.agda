------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.8 for the K-free rules of P′, at every width 4 + m, from the
-- facts about the decoded consecutive letters
--
-- The decoding (Decoding) is the generic chain decoding of
-- Lemma88.Chains at the placed gadgets of a width; Lemma88.Fragment
-- derives every K-free rule from `Facts`.  So at a width where the
-- consecutive facts hold — phase gadgets commuting, of order four and
-- inverted by their flips, the rotations inverse, px-sq, px-conj₂ on
-- one pair, px-conj on adjacent pairs, far letters commuting, and the
-- braid — every K-free rule of P′ decodes to an equation of circuits.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.Lemma88.KFree (m : ℕ) where

open import Word.Base using (Word ; _ʷ)

open import Notations using (₄₊)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Numbering (₄₊ m) using (N)
open import Examples.Groups.Clifford+CS.Auxiliary.Fragment using (_F,_===_)
open import Examples.Groups.Clifford+CS.Decoding m
  using (dPP₁ ; dPP₁′ ; lo₁ ; hi₁ ; dKI₁ ; d)
import Examples.Groups.Clifford+CS.Lemma88.Fragment as Fr

private
  module F = Fr ((₄₊ m) VRel,_===_) N dPP₁ dPP₁′ lo₁ hi₁ dKI₁

-- The consecutive facts at this width.
Facts : Set
Facts = F.Facts

-- Lemma 8.8 for the K-free rules, given the facts.
k-free : Facts → ∀ {u t} → N F, u === t → (₄₊ m) ⊢ (d ʷ) u ≈ (d ʷ) t
k-free fs = F.Proofs.fragment fs
