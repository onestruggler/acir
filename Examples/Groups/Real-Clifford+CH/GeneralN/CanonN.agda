------------------------------------------------------------------------
-- Presentations of groups
--
-- The canonical box facts of BoxFrames on five wires or more
--
-- At width 5 + k, from completeness at every width below (the global
-- induction's hypothesis, `Completes (1 + k)`): the involution (299),
-- X on the box wire (H by (285), Z by the schema (19)), the networks
-- on the controls ((307), `sym-net`), the merge (309) followed by
-- (274), and (336).  So BoxFrames and Lemma 8.4 hold there.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.CanonN
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ ; zero ; suc ; s≤s ; z≤n)
open import Data.Nat.Properties using (≤-refl)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; ax)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZXPass complete₂ complete₃ using (Complete ; box274)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Keystone complete₂ complete₃ using (eq285ₙ)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFull complete₂ complete₃ using (eq299)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃
  using (Completes ; eq307 ; sym-net ; eqSymAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxMergeAt complete₂ complete₃ using (merge-at)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxForms complete₂ complete₃ using (eq336)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon ; pass)

canonN : ∀ k → Completes (₁₊ k) → Canon (₂₊ k)
canonN k cs = record
  { invol   = eq299 (₁₊ k) c
  ; x-box   = sym (pass (sym (eq285ₙ (₁₊ k) c)) (pass (sym (ax (box-Z k))) (sym (eq285ₙ (₁₊ k) c))))
  ; swaps   = sym-net (₁₊ k) (eq307 (₁₊ k) cs)
  ; merge   = trans (merge-at k c (eqSymAt (₁₊ k) cs) 0 (s≤s z≤n))
                    (trans (cong left-unit (back _ right-unit)) (box274 (₁₊ k) c))
  ; wire274 = box274 (₁₊ k) c
  ; comm336 = eq336 k c
  }
  where
  open Tools ((suc (₄₊ k)) VRel,_===_)
  c : Complete (₁₊ k)
  c = cs ≤-refl
