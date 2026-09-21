------------------------------------------------------------------------
-- Presentations of groups
--
-- The box wire of the multi-controlled box is an identity wire
-- (Clément, Lemma D.8, Equation (274))
--
-- The box does not depend on which wire carries its box: the swap of
-- the box wire with an idle wire below it leaves the gate unchanged.
--
-- The proof is the five-qubit (251) at every width, and just as short,
-- because the swap IS a word in CZ and H — Equation (8) is how `Ex` is
-- spelled in `Syntactics`, so `Ex ↓` unfolds to
--
--     CZ ↓ • H ↓ • H ↑ • CZ ↓ • H ↓ • H ↑ • CZ ↓ • H ↓ • H ↑
--
-- definitionally.  The box one wire up passes each letter: the CZ by
-- (272), H on the idle wire 0 because it touches nothing of the gate,
-- and H on wire 1 — the box wire — by (285), H on the box wire passes
-- the box.  That last one is the keystone of Lemma D.8 and is not yet
-- available at every width, so it is a hypothesis here: at k = 0 it is
-- the four-qubit (155), and in the paper's induction on the width it
-- comes from the previous level, which is why the paper cites it as
-- (285)ₙ₋₁.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.BoxWire
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; Ex²)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Box complete₂ complete₃
  using (eq155)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box complete₂ complete₃
  using (eq272)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  variable
    k n : ℕ

------------------------------------------------------------------------
-- (285) at the sizes where it is already known
--
-- H on the box wire passes the box: the four-qubit (155) is the box
-- with three controls, the first case of the schema.

Eq285 : ℕ → Set
Eq285 k = (₄₊ k) ⊢ H ↓ • Λ□ (₃₊ k) ≈ Λ□ (₃₊ k) • H ↓

eq285-0 : Eq285 0
eq285-0 = eq155

------------------------------------------------------------------------
-- The box passes the swap of its box wire with the idle wire below

box-Ex : ∀ k → Eq285 k → (₁₊ (₄₊ k)) ⊢ Ex ↓ • (Λ□ (₃₊ k) ↑) ≈ (Λ□ (₃₊ k) ↑) • Ex ↓
box-Ex k e285 = sym (comm-• c (comm-• h₀ (comm-• h₁ (comm-• c (comm-• h₀
                    (comm-• h₁ (comm-• c (comm-• h₀ h₁))))))))
  where
  open Tools ((₁₊ (₄₊ k)) VRel,_===_)
  open WordAlgebra ((₁₊ (₄₊ k)) VRel,_===_)

  box : Circuit (₁₊ (₄₊ k))
  box = Λ□ (₃₊ k) ↑

  c : box • CZ ↓ ≈ CZ ↓ • box
  c = sym (eq272 k)

  -- Wire 0 is idle for the shifted box.
  h₀ : box • H ↓ ≈ H ↓ • box
  h₀ = comm-gate₁-w↑ H-gate (Λ□ (₃₊ k))

  -- Wire 1 is the box wire.
  h₁ : box • H ↑ ≈ H ↑ • box
  h₁ = sym (lemma-cong↑ (H ↓ • Λ□ (₃₊ k)) (Λ□ (₃₊ k) • H ↓) e285)

------------------------------------------------------------------------
-- (274)

eq274 : ∀ k → Eq285 k →
        (₁₊ (₄₊ k)) ⊢ Ex ↓ • (Λ□ (₃₊ k) ↑) • Ex ↓ ≈ Λ□ (₃₊ k) ↑
eq274 k e285 = begin
  Ex ↓ • (Λ□ (₃₊ k) ↑) • Ex ↓       ≈⟨ sym assoc ⟩
  (Ex ↓ • Λ□ (₃₊ k) ↑) • Ex ↓       ≈⟨ front _ (box-Ex k e285) ⟩
  ((Λ□ (₃₊ k) ↑) • Ex ↓) • Ex ↓     ≈⟨ cancelʳ _ Ex² ⟩
  Λ□ (₃₊ k) ↑ ∎
  where open Tools ((₁₊ (₄₊ k)) VRel,_===_)
