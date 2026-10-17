------------------------------------------------------------------------
-- Presentations of groups
--
-- The six-wire switches on any six wires of a wider circuit
--
-- The step of the stability theorem at a width n ≥ 6 re-borrows S-boxes
-- (the joint paper's switch (i)): an S-box's box wire or borrowed wire
-- moves to an idle wire.  Stable.Six.Su and Stable.Six.Sa are those
-- moves on six wires, from completeness on five; an equation between
-- six-wire lines holds on the bottom six wires of any wider circuit
-- (Stable.Weakening.topᵏ-congᵧ) and then on any six wires, placed by a
-- network (`wide`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Semantics using (_~_)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_⊢ᵧ_≈_)

module Examples.Groups.Clifford+CS.Stable.Six.Wide
  (c₅ : ∀ {u v : Circuit 5} → ⟦ u ⟧ ~ ⟦ v ⟧ → 5 ⊢ᵧ u ≈ v) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Word.Base using (Word)

import Presentation.Base as PB
import Examples.Groups.Symmetric.Syntactics as S

open import Examples.Groups.Clifford+CS.TopWeakening using (topᵏ)
open import Examples.Groups.Clifford+CS.LocalPlace using (pl)
open import Examples.Groups.Clifford+CS.Five.Letters using (b-Sb2-0-41-3)
open import Examples.Groups.Clifford+CS.Stable.Weakening using (topᵏ-congᵧ)
open import Examples.Groups.Clifford+CS.Stable.Six.Engine using (PG ; g5 ; ⟪_⟫₆)
open import Examples.Groups.Clifford+CS.Stable.Six.Su c₅ using (su)
open import Examples.Groups.Clifford+CS.Stable.Six.Sa c₅ using (sa)

-- An equation between six-wire lines, on any six wires of m + 6.
wide : ∀ m (σ : Word (S.Gen (m +ℕ 6))) (xs ys : List PG) → 6 ⊢ᵧ ⟪ xs ⟫₆ ≈ ⟪ ys ⟫₆ →
       (m +ℕ 6) ⊢ᵧ pl σ (topᵏ m ⟪ xs ⟫₆) ≈ pl σ (topᵏ m ⟪ ys ⟫₆)
wide m σ xs ys e = PB.cong PB.refl (PB.cong (topᵏ-congᵧ m e) PB.refl)

-- Σ(1; 5, 2 | 3, 4) with its box wire moved to wire 0, and with its
-- borrowed wire moved to wire 0, on any six wires.
su-wide : ∀ m (σ : Word (S.Gen (m +ℕ 6))) →
          (m +ℕ 6) ⊢ᵧ pl σ (topᵏ m ⟪ g5 (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []) b-Sb2-0-41-3 ∷ [] ⟫₆)
                    ≈ pl σ (topᵏ m ⟪ g5 (0 ∷ 1 ∷ 3 ∷ 4 ∷ []) b-Sb2-0-41-3 ∷ [] ⟫₆)
su-wide m σ = wide m σ (g5 (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []) b-Sb2-0-41-3 ∷ []) (g5 (0 ∷ 1 ∷ 3 ∷ 4 ∷ []) b-Sb2-0-41-3 ∷ []) su

sa-wide : ∀ m (σ : Word (S.Gen (m +ℕ 6))) →
          (m +ℕ 6) ⊢ᵧ pl σ (topᵏ m ⟪ g5 (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []) b-Sb2-0-41-3 ∷ [] ⟫₆)
                    ≈ pl σ (topᵏ m ⟪ g5 (0 ∷ 1 ∷ 2 ∷ 4 ∷ []) b-Sb2-0-41-3 ∷ [] ⟫₆)
sa-wide m σ = wide m σ (g5 (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []) b-Sb2-0-41-3 ∷ []) (g5 (0 ∷ 1 ∷ 2 ∷ 4 ∷ []) b-Sb2-0-41-3 ∷ []) sa
