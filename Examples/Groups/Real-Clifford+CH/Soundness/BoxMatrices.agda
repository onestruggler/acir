------------------------------------------------------------------------
-- Presentations of groups
--
-- The stored matrices behind the semantics of the multi-controlled box
--
-- Five identities of 8 × 8 integer matrices, and the three base cases
-- of the box, each checked by `refl` (Soundness.Box explains what they
-- say).  They are the expensive part of that proof, so they live here,
-- checked once, and behind `abstract`: outside this module the stored
-- matrices never unfold, so nothing downstream can recompute them.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Soundness.BoxMatrices where

open import Data.Bool using (_∧_)
open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Examples.Groups.Real-Clifford+CH.Semantics
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation
open import Examples.Groups.Real-Clifford+CH.Soundness.Operators

------------------------------------------------------------------------
-- The three-wire identities behind the recursive step
--
-- With D the phase −1 on |1⟩ of wire 0 (what the (k + 2)-controlled
-- box contributes when its controls are set) and I the identity (when
-- they are not): CCZX · D · CCXZ · D is the phase −1 on wires 1 and 2
-- both set, and CCZX · CCXZ is the identity, each up to the power of √2
-- the two words carry.

z₀ ccz : Bits 3 → 𝔽
z₀  (a ∷ _ ∷ _ ∷ []) = sgn a
ccz (_ ∷ b ∷ c ∷ []) = sgn (b ∧ c)

-- The three-wire words at their own width, as closed circuits: the one
-- spelling that every stored matrix, and every use of one, refers to.
CCZX₀ CCXZ₀ τ₀₂₀ : Circuit 3
CCZX₀ = CCZX
CCXZ₀ = CCXZ
τ₀₂₀  = τ₀₂

-- The numbers of letters, and the powers of √2 the words carry.
ℓC ℓτ : ℕ
ℓC = len CCZX₀ +ℕ len CCXZ₀
ℓτ = len τ₀₂₀

cC cτ : 𝔽
cC = √2^ ℓC
cτ = √2^ ℓτ

abstract
  Cm C′m D3 : Mat 3
  Cm  = ⟦ CCZX₀ ⟧M
  C′m = ⟦ CCXZ₀ ⟧M
  D3  = matOf (diag z₀)

  Cm-def : ⟦ CCZX₀ ⟧M ≡ Cm
  Cm-def = Eq.refl

  C′m-def : ⟦ CCXZ₀ ⟧M ≡ C′m
  C′m-def = Eq.refl

  D3-ix : ix D3 ≐ diag z₀
  D3-ix = ix-matOf (diag z₀)

  step-set : mulM Cm (mulM D3 (mulM C′m D3)) ≡ scaleM cC (matOf (diag ccz))
  step-set = Eq.refl

  step-unset : mulM Cm (mulM idM (mulM C′m idM)) ≡ scaleM cC idM
  step-unset = Eq.refl

  -- The transposition, as a circuit, is the permutation matrix.
  τ-perm : ⟦ τ₀₂₀ ⟧M ≡ scaleM cτ permM
  τ-perm = Eq.refl

  -- The base cases: the box on 0, 1 and 2 controls.
  b0 : ⟦ Λ□ 0 ⟧M ≡ scaleM (√2^ len (Λ□ 0)) (matOf (diag (phase 0)))
  b0 = Eq.refl

  b1 : ⟦ Λ□ 1 ⟧M ≡ scaleM (√2^ len (Λ□ 1)) (matOf (diag (phase 1)))
  b1 = Eq.refl

  b2 : ⟦ Λ□ 2 ⟧M ≡ scaleM (√2^ len (Λ□ 2)) (matOf (diag (phase 2)))
  b2 = Eq.refl
