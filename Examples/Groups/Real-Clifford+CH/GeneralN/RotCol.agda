------------------------------------------------------------------------
-- Presentations of groups
--
-- The rotations of the decoding, and their placed commutation
-- (Clément, Appendix E.5)
--
-- `rot β` is the multi-controlled ZX (β true) or XZ (β false) on wire 0,
-- controlled by every other wire — the base gate of the decoded
-- (−1)_[a] X_[a,a+1] (`mc±XZ β L = conj₁ L (rot β)`, `mc±XZ-rot`).
-- `RotComm m` says that two such rotations, placed and coloured, commute
-- when their colourings differ on a wire off both targets: the paper's
-- (351) and (352) with x ≠ y, in every position.  Like Col, this module
-- has no parameters, so that the proof at width 5 + k (RotAnywhere) and
-- the rules that use it (Lemma88.Rule32) spell the statement alike.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.RotCol where

open import Data.Bool using (Bool ; true ; false)
open import Data.Fin using (Fin ; toℕ) renaming (zero to 0F)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (perm)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (Layout ; conj₁ ; mc±XZ)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (place)

rot : ∀ {m} → Bool → Circuit (₃₊ m)
rot {m} true  = ΛZX (₂₊ m)
rot {m} false = ΛXZ (₂₊ m)

mc±XZ-rot : ∀ {m} β (L : Layout (₃₊ m)) → mc±XZ β L ≡ conj₁ L (rot β)
mc±XZ-rot true  L = Eq.refl
mc±XZ-rot false L = Eq.refl

RotComm : ℕ → Set
RotComm m =
  ∀ α β (u u′ : Word (S.Gen (₃₊ m))) (t t′ : Fin (₃₊ m)) → perm u ⟨$⟩ʳ t ≡ 0F → perm u′ ⟨$⟩ʳ t′ ≡ 0F →
  (s s′ : Bits (₃₊ m)) → lookupℕ (toℕ t) s ≡ true → lookupℕ (toℕ t′) s′ ≡ true →
  (j : Fin (₃₊ m)) → j ≢ t → j ≢ t′ → lookupℕ (toℕ j) s ≢ lookupℕ (toℕ j) s′ →
  (₃₊ m) ⊢ place u s (rot α) • place u′ s′ (rot β) ≈ place u′ s′ (rot β) • place u s (rot α)
