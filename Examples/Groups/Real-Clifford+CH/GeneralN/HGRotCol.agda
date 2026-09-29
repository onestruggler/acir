------------------------------------------------------------------------
-- Presentations of groups
--
-- A placed rotation against the gadget, as a statement (Clément,
-- Appendix E.5, rule (38))
--
-- The gadget of Definition 8.3, the decoded H_[0,1] H_[3,2], is the H
-- gate with its H on wire 0 and its box wire 1 (Layout's S, the H gate
-- under the swap of the wires 0 1), every other control white (`gcol`).
-- `HGRot m` says that a rotation placed on any target t and coloured s
-- commutes with it as soon as s is black on some wire j ≥ 2 other than
-- t, where the gadget is white: the paper's (348)–(350) with x ≠ y.
-- Like RotCol, this module has no parameters, so that the proof at width
-- 5 + k (HGAnywhere) and the rule that uses it (Lemma88.Rule38) spell
-- the statement alike.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.HGRotCol where

open import Data.Bool using (true ; false)
open import Data.Fin using (Fin ; toℕ) renaming (zero to 0F)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Nat using (ℕ ; _≤_)
open import Data.Vec using (_∷_ ; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_)
open import Word.Base using (Word ; _•_)

open import Notations using (₁₊ ; ₃₊)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (perm)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (place)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot)

-- The gadget's colouring, and the gadget.
gcol : ∀ m → Bits (₃₊ m)
gcol m = true ∷ true ∷ replicate (₁₊ m) false

gadgetG : ∀ m → Circuit (₃₊ m)
gadgetG m = col (gcol m) (Ex ↓ • ΛH (₁₊ m) • Ex ↓)

HGRot : ℕ → Set
HGRot m =
  ∀ β (u : Word (S.Gen (₃₊ m))) (t : Fin (₃₊ m)) → perm u ⟨$⟩ʳ t ≡ 0F → (s : Bits (₃₊ m)) →
  lookupℕ (toℕ t) s ≡ true → (j : Fin (₃₊ m)) → 2 ≤ toℕ j → j ≢ t → lookupℕ (toℕ j) s ≡ true →
  (₃₊ m) ⊢ place u s (rot β) • gadgetG m ≈ gadgetG m • place u s (rot β)
