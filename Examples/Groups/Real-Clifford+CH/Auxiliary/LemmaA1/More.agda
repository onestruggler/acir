------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma A.1: (d1) and the variant (d2†) (Clément, Appendix A.2)
--
-- The paper's chains, generated and checked numerically as those of
-- LemmaA1.Base (LemmaA1/gen: gen_chain.py, spec_more.py).  (d2†) uses
-- (a1) at any index and (d1) uses (b1), both from LemmaA1.Moves.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.LemmaA1.More (N : ℕ) where

open import Data.Fin using (Fin)
open import Data.List using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Word.Base using (_•_)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Syntactics using (−1 ; X ; H ; _G,_===_)
open _G,_===_
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SegChain (N G,_===_)
  using (at ; _▸_ ; done ; run)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.LemmaA1.Base N using (sy ; e1)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.LemmaA1.Moves using (a1 ; b1)

open Tools (N G,_===_)

-- (d2†): a sign on the second index of a Hadamard, moved before it.
d2† : ∀ {a b : Fin N} → a ≢ b → H a b • −1 b ≈ X a b • H a b
d2† {a} {b} ab =
  run {H a b ∷ −1 b ∷ []}
      {X a b ∷ H a b ∷ []}
    ( at 2 0 (H a b ∷ H a b ∷ []) (sym (axiom (a3 ab))) ▸
      at 3 0 (X a b ∷ X a b ∷ []) (sym (axiom (a2 ab))) ▸
      at 2 2 (−1 b ∷ H a b ∷ []) (sym (axiom (d2 ab))) ▸
      at 1 2 ([]) (a1 b) ▸
      at 0 2 ([]) (axiom (a3 ab)) ▸
      done)

-- (d1): the two signs of a Hadamard pass it.
d1 : ∀ {a b : Fin N} → a ≢ b → −1 a • −1 b • H a b ≈ H a b • −1 a • −1 b
d1 {a} {b} ab =
  run {−1 a ∷ −1 b ∷ H a b ∷ []}
      {H a b ∷ −1 a ∷ −1 b ∷ []}
    ( at 1 2 (H a b ∷ X a b ∷ []) (axiom (d2 ab)) ▸
      at 2 1 (X b a ∷ []) (e1 ab) ▸
      at 1 2 (X b a ∷ H b a ∷ []) (axiom (e2* (sy ab))) ▸
      at 1 0 (H b a ∷ H b a ∷ []) (sym (axiom (a3 (sy ab)))) ▸
      at 0 2 (H b a ∷ X b a ∷ []) (axiom (d2 (sy ab))) ▸
      at 2 2 (−1 a ∷ H b a ∷ []) (sym (axiom (d2 (sy ab)))) ▸
      at 3 2 ([]) (axiom (a3 (sy ab))) ▸
      at 1 1 (X a b ∷ []) (e1 (sy ab)) ▸
      at 0 2 (X a b ∷ H a b ∷ []) (axiom (e2* ab)) ▸
      at 0 0 (H a b ∷ H a b ∷ []) (sym (axiom (a3 ab))) ▸
      at 1 2 (−1 b ∷ H a b ∷ []) (sym (axiom (d2 ab))) ▸
      at 2 2 ([]) (axiom (a3 ab)) ▸
      at 1 2 (−1 a ∷ −1 b ∷ []) (b1 (sy ab)) ▸
      done)
