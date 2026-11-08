{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Errata where

open import Data.Empty using (⊥)
open import Data.Integer.Base using (+_ ; -[1+_])
open import Data.Bool.Base using (true ; false)
open import Data.Vec.Base using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≢_)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.GateMatrices
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.Evaluation

-- Witness: matrix entry (1, 1).
r033-false : ⟦ CCX01 ⟧ ~ ⟦ SWAP12 • CCX02 • SWAP02 ⟧ → ⊥
r033-false eq = bad (Eq.trans
  (Eq.sym (Eq.cong (λ M → √2^ len (SWAP12 • CCX02 • SWAP02) * ix M (false ∷ false ∷ true ∷ []) (false ∷ false ∷ true ∷ [])) e56))
  (Eq.trans (eq (false ∷ false ∷ true ∷ []) (false ∷ false ∷ true ∷ []))
    (Eq.cong (λ M → √2^ len (CCX01) * ix M (false ∷ false ∷ true ∷ []) (false ∷ false ∷ true ∷ [])) e261)))
  where
  bad : ((+ 1) +√2 (+ 0)) ≢ ((+ 0) +√2 (+ 0))
  bad ()

-- Witness: matrix entry (0, 0).
m0-alias-false : ⟦ m0 ⟧ ~ ⟦ X0 • X1 • CCZ • X1 • X0 ⟧ → ⊥
m0-alias-false eq = bad (Eq.trans
  (Eq.sym (Eq.cong (λ M → √2^ len (X0 • X1 • CCZ • X1 • X0) * ix M (false ∷ false ∷ false ∷ []) (false ∷ false ∷ false ∷ [])) e130))
  (Eq.trans (eq (false ∷ false ∷ false ∷ []) (false ∷ false ∷ false ∷ []))
    (Eq.cong (λ M → √2^ len (m0) * ix M (false ∷ false ∷ false ∷ []) (false ∷ false ∷ false ∷ [])) e264)))
  where
  bad : ((-[1+ 0 ]) +√2 (+ 0)) ≢ ((+ 1) +√2 (+ 0))
  bad ()

-- Witness: matrix entry (3, 3).
t67-alias-false : ⟦ t67 ⟧ ~ ⟦ CCX12 ⟧ → ⊥
t67-alias-false eq = bad (Eq.trans
  (Eq.sym (Eq.cong (λ M → √2^ len (CCX12) * ix M (false ∷ true ∷ true ∷ []) (false ∷ true ∷ true ∷ [])) e56))
  (Eq.trans (eq (false ∷ true ∷ true ∷ []) (false ∷ true ∷ true ∷ []))
    (Eq.cong (λ M → √2^ len (t67) * ix M (false ∷ true ∷ true ∷ []) (false ∷ true ∷ true ∷ [])) e18)))
  where
  bad : ((+ 1) +√2 (+ 0)) ≢ ((+ 0) +√2 (+ 0))
  bad ()

-- Witness: matrix entry (1, 0).
r097-false : ⟦ t01 • NK ⟧ ~ ⟦ NK • t01 • m1 • m3 ⟧ → ⊥
r097-false eq = bad (Eq.trans
  (Eq.sym (Eq.cong (λ M → √2^ len (NK • t01 • m1 • m3) * ix M (false ∷ false ∷ true ∷ []) (false ∷ false ∷ false ∷ [])) e182))
  (Eq.trans (eq (false ∷ false ∷ true ∷ []) (false ∷ false ∷ false ∷ []))
    (Eq.cong (λ M → √2^ len (t01 • NK) * ix M (false ∷ false ∷ true ∷ []) (false ∷ false ∷ false ∷ [])) e266)))
  where
  bad : ((+ 2) +√2 (+ 0)) ≢ ((-[1+ 1 ]) +√2 (+ 0))
  bad ()

-- Witness: matrix entry (0, 3).
r100-false : ⟦ NK • k1345 ⟧ ~ ⟦ k1345 • NK ⟧ → ⊥
r100-false eq = bad (Eq.trans
  (Eq.sym (Eq.cong (λ M → √2^ len (k1345 • NK) * ix M (false ∷ false ∷ false ∷ []) (false ∷ true ∷ true ∷ [])) e215))
  (Eq.trans (eq (false ∷ false ∷ false ∷ []) (false ∷ true ∷ true ∷ []))
    (Eq.cong (λ M → √2^ len (NK • k1345) * ix M (false ∷ false ∷ false ∷ []) (false ∷ true ∷ true ∷ [])) e267)))
  where
  bad : ((+ 0) +√2 (+ 0)) ≢ ((+ 8) +√2 (+ 0))
  bad ()

