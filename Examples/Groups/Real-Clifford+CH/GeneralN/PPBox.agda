------------------------------------------------------------------------
-- Presentations of groups
--
-- P ⊗ P on the box wire and an idle wire below passes the box
-- (Clément, Lemma D.8, Equation (276))
--
-- The paper's proof: write the box, one wire up, in its E-form (284)
-- one width down; P ⊗ P on the wires 0 1 exchanges the doubly
-- controlled ZX and XZ one wire up, (174); and P ⊗ P on the wires 0 1
-- turns the multi-controlled H one wire up into the box B one wire up
-- — the step the paper takes by Lemma 5.1, here completeness one width
-- down with wire 3 idle.  What is left is P ⊗ P squared and the box in
-- its mirrored B-form, (286).
--
-- The step is the only place anything is computed.  One width down it
-- is P ⊗ P on the wires 0 1 and 1 2 around the box on wire 2 with its
-- first control on wire 1: a payload identity on three wires, decided
-- by CForm.  Placed on the wires other than 3, the P ⊗ P stay where
-- they are (Place.place-low), and the box becomes B one wire up because
-- the two networks that carry wire 3 to wire 0 around it have the same
-- permutation (PermCalc) up to a swap below it.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.PPBox
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Fin using (zero ; suc)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; Ex²)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Blocks complete₂ using (L-sem)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃ using (eq174)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box complete₂ complete₃ using (eq286)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CForm
open import Examples.Groups.Real-Clifford+CH.GeneralN.Locals
open import Examples.Groups.Real-Clifford+CH.GeneralN.Sem using (B□ ; E□ ; cf-Λ↑ ; sem284)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place
open import Examples.Groups.Real-Clifford+CH.GeneralN.Networks using (scyc ; scyc⁻¹)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (perm-≈)

-- (276): P ⊗ P on the box wire and the idle wire below it.
Eq276 : ℕ → Set
Eq276 k = (₁₊ (₄₊ k)) ⊢ PP ↓ • Λ□ (₃₊ k) ↑ • PP ↓ ≈ Λ□ (₃₊ k) ↑

module _ (k : ℕ) (complete : ∀ {u v : Circuit (₄₊ k)} → ⟦ u ⟧ ~ ⟦ v ⟧ → (₄₊ k) ⊢ u ≈ v) where

  private
    open Tools ((₁₊ (₄₊ k)) VRel,_===_)

    PP² : (₁₊ (₄₊ k)) ⊢ PP ↓ • PP ↓ ≈ ε
    PP² = L-sem (PP • PP) ε Eq.refl

    -- (174) the other way round.
    eq174′ : (₁₊ (₄₊ k)) ⊢ PP ↓ • CCXZ ↑ ≈ CCZX ↑ • PP ↓
    eq174′ = begin
      PP ↓ • CCXZ ↑                         ≈⟨ back _ (sym (cancelʳ (CCXZ ↑) PP²)) ⟩
      PP ↓ • ((CCXZ ↑ • PP ↓) • PP ↓)       ≈⟨ back _ (front _ (sym eq174)) ⟩
      PP ↓ • ((PP ↓ • CCZX ↑) • PP ↓)       ≈⟨ by-passoc (□ • ((□ • □) • □)) ((□ • □) • □ • □) Eq.refl ⟩
      (PP ↓ • PP ↓) • CCZX ↑ • PP ↓         ≈⟨ front _ PP² ⟩
      ε • CCZX ↑ • PP ↓                     ≈⟨ left-unit ⟩
      CCZX ↑ • PP ↓ ∎

    --------------------------------------------------------------------
    -- The step, one width down with wire 3 idle

    -- The box B one wire up, with its idle wire 3 removed: the box on
    -- wire 2 with its first control on wire 1.
    y : Circuit (₄₊ k)
    y = Ex ↑ • Λ□ (₂₊ k) ↑ • Ex ↑

    u : Circuit (₄₊ k)
    u = PP ↓ • PP ↑ • y • PP ↑ • PP ↓

    cf-y : CF {3} {₁₊ k} y
    cf-y = cf-• (cf-loc′ (Ex ↑) Ex₁₂ᴸ Ex₁₂ᴸ-def) (cf-• (cf-Λ↑ k) (cf-loc′ (Ex ↑) Ex₁₂ᴸ Ex₁₂ᴸ-def))

    cf-u : CF {3} {₁₊ k} u
    cf-u = cf-• pp₀₁ (cf-• pp₁₂ (cf-• cf-y (cf-• pp₁₂ pp₀₁)))
      where
      pp₀₁ : CF {3} {₁₊ k} (PP ↓)
      pp₀₁ = cf-loc′ PP PP₀₁ᴸ PP₀₁ᴸ-def
      pp₁₂ : CF {3} {₁₊ k} (PP ↑)
      pp₁₂ = cf-loc′ (PP ↑) PP₁₂ᴸ PP₁₂ᴸ-def

    sem-step : ⟦ u ⟧ ~ ⟦ y ⟧
    sem-step = cf-~ cf-u cf-y Eq.refl Eq.refl

    -- Placed on the wires other than 3.
    place-u : (₁₊ (₄₊ k)) ⊢ place 3 u ≈ PP ↓ • PP ↑ • place 3 y • PP ↑ • PP ↓
    place-u = begin
      place 3 u
        ≈⟨ place-• 3 (PP ↓) (PP ↑ • y • PP ↑ • PP ↓) ⟩
      place 3 (PP ↓) • place 3 (PP ↑ • y • PP ↑ • PP ↓)
        ≈⟨ back _ (place-• 3 (PP ↑) (y • PP ↑ • PP ↓)) ⟩
      place 3 (PP ↓) • place 3 (PP ↑) • place 3 (y • PP ↑ • PP ↓)
        ≈⟨ back _ (back _ (place-• 3 y (PP ↑ • PP ↓))) ⟩
      place 3 (PP ↓) • place 3 (PP ↑) • place 3 y • place 3 (PP ↑ • PP ↓)
        ≈⟨ back _ (back _ (back _ (place-• 3 (PP ↑) (PP ↓)))) ⟩
      place 3 (PP ↓) • place 3 (PP ↑) • place 3 y • place 3 (PP ↑) • place 3 (PP ↓)
        ≈⟨ cong (place-low 3 PP)
                (cong (place-low 3 (PP ↑))
                      (back _ (cong (place-low 3 (PP ↑)) (place-low 3 PP)))) ⟩
      PP ↓ • PP ↑ • place 3 y • PP ↑ • PP ↓ ∎

    -- The two networks that carry wire 3 to wire 0 around the box, and
    -- back, have the same permutations.
    N≈ : (₁₊ (₄₊ k)) ⊢ cyc⁻¹ 3 • Ex ↑ ↑ ≈ τ₀₂ ↑ • Ex ↓
    N≈ = perm-≈ {u = scyc⁻¹ 3 • (S.σ S.↑) S.↑} {v = (S.σ • S.σ S.↑ • S.σ) S.↑ • S.σ}
           (λ { zero → Eq.refl ; (suc zero) → Eq.refl ; (suc (suc zero)) → Eq.refl
              ; (suc (suc (suc zero))) → Eq.refl ; (suc (suc (suc (suc _)))) → Eq.refl })

    M≈ : (₁₊ (₄₊ k)) ⊢ Ex ↑ ↑ • cyc 3 ≈ Ex ↓ • τ₀₂ ↑
    M≈ = perm-≈ {u = (S.σ S.↑) S.↑ • scyc 3} {v = S.σ • (S.σ • S.σ S.↑ • S.σ) S.↑}
           (λ { zero → Eq.refl ; (suc zero) → Eq.refl ; (suc (suc zero)) → Eq.refl
              ; (suc (suc (suc zero))) → Eq.refl ; (suc (suc (suc (suc _)))) → Eq.refl })

    place-y : (₁₊ (₄₊ k)) ⊢ place 3 y ≈ B□ k ↑
    place-y = begin
      cyc⁻¹ 3 • (Ex ↑ ↑ • Λ₂↑ • Ex ↑ ↑) • cyc 3
        ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (cyc⁻¹ 3 • Ex ↑ ↑) • Λ₂↑ • (Ex ↑ ↑ • cyc 3)
        ≈⟨ cong N≈ (back _ M≈) ⟩
      (τ₀₂ ↑ • Ex ↓) • Λ₂↑ • (Ex ↓ • τ₀₂ ↑)
        ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □) • □ • □) Eq.refl ⟩
      τ₀₂ ↑ • (Ex ↓ • Λ₂↑) • Ex ↓ • τ₀₂ ↑
        ≈⟨ back _ (front _ (low-comm Ex (Λ□ (₂₊ k)))) ⟩
      τ₀₂ ↑ • (Λ₂↑ • Ex ↓) • Ex ↓ • τ₀₂ ↑
        ≈⟨ by-passoc (□ • (□ • □) • □ • □) (□ • □ • (□ • □) • □) Eq.refl ⟩
      τ₀₂ ↑ • Λ₂↑ • (Ex ↓ • Ex ↓) • τ₀₂ ↑
        ≈⟨ back _ (back _ (front _ Ex²)) ⟩
      τ₀₂ ↑ • Λ₂↑ • ε • τ₀₂ ↑
        ≈⟨ back _ (back _ left-unit) ⟩
      τ₀₂ ↑ • Λ₂↑ • τ₀₂ ↑ ∎
      where
      Λ₂↑ : Circuit (₁₊ (₄₊ k))
      Λ₂↑ = Λ□ (₂₊ k) ↑ ↑

    -- The step itself: P ⊗ P on the wires 0 1 turns the multi-controlled
    -- H one wire up into the box B one wire up.
    core : (₁₊ (₄₊ k)) ⊢ PP ↓ • PP ↑ • B□ k ↑ • PP ↑ • PP ↓ ≈ B□ k ↑
    core = begin
      PP ↓ • PP ↑ • B□ k ↑ • PP ↑ • PP ↓      ≈⟨ back _ (back _ (front _ (sym place-y))) ⟩
      PP ↓ • PP ↑ • place 3 y • PP ↑ • PP ↓   ≈⟨ sym place-u ⟩
      place 3 u                               ≈⟨ lemma-5-1 3 complete sem-step ⟩
      place 3 y                               ≈⟨ place-y ⟩
      B□ k ↑ ∎

    step : (₁₊ (₄₊ k)) ⊢ PP ↓ • E□ k ↑ ≈ B□ k ↑ • PP ↓
    step = begin
      PP ↓ • PP ↑ • B□ k ↑ • PP ↑                 ≈⟨ sym (cancelʳ _ PP²) ⟩
      ((PP ↓ • PP ↑ • B□ k ↑ • PP ↑) • PP ↓) • PP ↓ ≈⟨ front _ (trans (by-passoc ((□ • □ • □ • □) • □) (□ • □ • □ • □ • □) Eq.refl) core) ⟩
      B□ k ↑ • PP ↓ ∎

  ----------------------------------------------------------------------
  -- (276)

  eq276 : Eq276 k
  eq276 = begin
    PP ↓ • Λ□ (₃₊ k) ↑ • PP ↓
      ≈⟨ back _ (front _ (lemma-cong↑ (Λ□ (₃₊ k)) (CCZX • E□ k • CCXZ • E□ k) (complete (sem284 k)))) ⟩
    PP ↓ • (CCZX ↑ • E□ k ↑ • CCXZ ↑ • E□ k ↑) • PP ↓
      ≈⟨ by-passoc (□ • (□ • □ • □ • □) • □) ((□ • □) • □ • □ • □ • □) Eq.refl ⟩
    (PP ↓ • CCZX ↑) • E□ k ↑ • CCXZ ↑ • E□ k ↑ • PP ↓
      ≈⟨ front _ eq174 ⟩
    (CCXZ ↑ • PP ↓) • E□ k ↑ • CCXZ ↑ • E□ k ↑ • PP ↓
      ≈⟨ by-passoc ((□ • □) • □ • □ • □ • □) (□ • (□ • □) • □ • □ • □) Eq.refl ⟩
    CCXZ ↑ • (PP ↓ • E□ k ↑) • CCXZ ↑ • E□ k ↑ • PP ↓
      ≈⟨ back _ (front _ step) ⟩
    CCXZ ↑ • (B□ k ↑ • PP ↓) • CCXZ ↑ • E□ k ↑ • PP ↓
      ≈⟨ by-passoc (□ • (□ • □) • □ • □ • □) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
    CCXZ ↑ • B□ k ↑ • (PP ↓ • CCXZ ↑) • E□ k ↑ • PP ↓
      ≈⟨ back _ (back _ (front _ eq174′)) ⟩
    CCXZ ↑ • B□ k ↑ • (CCZX ↑ • PP ↓) • E□ k ↑ • PP ↓
      ≈⟨ by-passoc (□ • □ • (□ • □) • □ • □) (□ • □ • □ • (□ • □) • □) Eq.refl ⟩
    CCXZ ↑ • B□ k ↑ • CCZX ↑ • (PP ↓ • E□ k ↑) • PP ↓
      ≈⟨ back _ (back _ (back _ (front _ step))) ⟩
    CCXZ ↑ • B□ k ↑ • CCZX ↑ • (B□ k ↑ • PP ↓) • PP ↓
      ≈⟨ by-passoc (□ • □ • □ • (□ • □) • □) (□ • □ • □ • □ • (□ • □)) Eq.refl ⟩
    CCXZ ↑ • B□ k ↑ • CCZX ↑ • B□ k ↑ • (PP ↓ • PP ↓)
      ≈⟨ back _ (back _ (back _ (back _ PP²))) ⟩
    CCXZ ↑ • B□ k ↑ • CCZX ↑ • B□ k ↑ • ε
      ≈⟨ back _ (back _ (back _ right-unit)) ⟩
    CCXZ ↑ • B□ k ↑ • CCZX ↑ • B□ k ↑
      ≈⟨ sym (lemma-cong↑ (Λ□ (₃₊ k)) (CCXZ • B□ k • CCZX • B□ k) (eq286 k)) ⟩
    Λ□ (₃₊ k) ↑ ∎
