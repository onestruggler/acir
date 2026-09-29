------------------------------------------------------------------------
-- Presentations of groups
--
-- The canonical form of rule (44) (Clément, Appendix E.5)
--
-- At width 5 + k, conjugated by the negations of the wires 2 …, rule
-- (44) says that the H gate SH — H on wire 1, box wire 0, the decoded
-- H_[0,1] H_[3,2] — passes C, the decoded X_[0,3] X_[1,2] (Canon361).
-- By (361) C is Λ • Y, the box on wire 0 times the rotation on wire 1
-- with wire 0 idle, and SH passes both:
--
-- * Λ by (338) with x = y (Box338Eq.XY);
-- * Y letter by letter, Y being B₂₁ • CH ↑ • B₂₁ • CH ↑ with B₂₁ the box
--   on wire 2 with wire 0 idle.  CH ↑ passes because between the swap it
--   is the CH from wire 2 to wire 0, which P ⊗ P on the wires 0 1 turns
--   into the CZ of those wires ((18)), and that CZ passes the box
--   ((273)).  B₂₁ passes because it is Λ times the box white on wire 2
--   ((309) on wire 1 and (274), moved to wire 2 by the swap of the wires
--   1 2, which the box passes), and the white box passes SH by (338) with
--   the colourings differing on wire 2 (Box338.sep).
--
-- This is not the paper's route, which goes through (360) and (111).
-- Checked numerically at four to seven wires first (scratchpad
-- r4x/r44_plan.py).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.Canon44
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (true ; false)
open import Data.Nat using (ℕ ; s≤s ; z≤n)
open import Data.Vec using (_∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; module S ; Ex² ; X² ; X²↑ ; S-X↓)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂ using (module PP↓ ; PP-CZ₂₀)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (σAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃ using (Completes)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CanonN complete₂ complete₃ using (canonN)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box complete₂ complete₃ using (eq273)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (Hg)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX353 complete₂ complete₃ using (allT)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box338 complete₂ complete₃ using (sep)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box338Eq complete₂ complete₃ using (module XY)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon361 complete₂ complete₃ using (C ; eq361)

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    N : ℕ
    N = ₁₊ (₄₊ k)

    completes : Completes (₁₊ k)
    completes j≤ = below (s≤s (s≤s (s≤s (s≤s j≤))))

    canon : Canon (₂₊ k)
    canon = canonN k completes

  open Tools (N VRel,_===_)

  -- The H gate: H on wire 1, box wire 0.
  SH : Circuit N
  SH = Ex ↓ • ΛH (₃₊ k) • Ex ↓

  private
    Λ B₂₁ : Circuit N
    Λ   = Λ□ (₄₊ k)
    B₂₁ = (Ex ↓ • Λ□ (₃₊ k) • Ex ↓) ↑

    ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
    ≡→≈ Eq.refl = refl

    pass₂ : ∀ {y a b : Circuit N} → y • a ≈ a • y → y • b ≈ b • y → y • (a • b) ≈ (a • b) • y
    pass₂ pa pb = trans (sym assoc) (trans (front _ pa) (trans assoc (trans (back _ pb) (sym assoc))))

    SH-Hg : SH ≈ Hg (₂₊ k)
    SH-Hg = XY.S-ΛH k below

    -- (338) with x = y.
    SH-Λ : SH • Λ ≈ Λ • SH
    SH-Λ = trans (front _ SH-Hg) (trans (sym (XY.eq338xy k below)) (back _ (sym SH-Hg)))

    -- CH on the wires 1 2: under the swap the CH from wire 2 to wire 0,
    -- which P ⊗ P turns into the CZ of those wires ((18)), which passes
    -- the box ((273)).
    A-CH₂₀ : ΛH (₃₊ k) • CH₂₀ ≈ CH₂₀ • ΛH (₃₊ k)
    A-CH₂₀ = PP↓.⟪⟫-≈ (sym (eq273 (₁₊ k))) (PP↓.⟪⟫-•₂ refl PP-CZ₂₀) (PP↓.⟪⟫-•₂ PP-CZ₂₀ refl)

    SH-CH : SH • CH ↑ ≈ CH ↑ • SH
    SH-CH = S.⟪⟫-≈ A-CH₂₀ (S.⟪⟫-•₂ refl (S.⟪⟫-⟪⟫ (CH ↑))) (S.⟪⟫-•₂ (S.⟪⟫-⟪⟫ (CH ↑)) refl)

    -- The box on wire 2 with wire 0 idle is Λ times its copy white on
    -- wire 2: (309) on wire 1 and (274) under the swap of the wires 1 2.
    module E₁ = Conj {N} (Ex ↑) (lemma-cong↑ _ _ Ex²)
    module X₂ = Conj {N} (X ↑ ↑) (lemma-cong↑ _ _ X²↑)

    Ex₁-Λ : Ex ↑ • Λ ≈ Λ • Ex ↑
    Ex₁-Λ = Canon.swaps canon (σAt 0)

    B₂₁-form : B₂₁ ≈ Λ • (X ↑ ↑ • Λ • X ↑ ↑)
    B₂₁-form = sym (E₁.⟪⟫-≈ (Canon.merge canon)
                            (E₁.⟪⟫-•₂ (E₁.⟪⟫-fix Ex₁-Λ) (E₁.⟪⟫-•₃ xs (E₁.⟪⟫-fix Ex₁-Λ) xs))
                            refl)
      where
      xs : E₁.⟪ X ↑ ⟫ ≈ X ↑ ↑
      xs = lemma-cong↑ _ _ S-X↓

    -- (338) with the colourings differing on wire 2.
    SH-Λw : SH • X₂.⟪ Λ ⟫ ≈ X₂.⟪ Λ ⟫ • SH
    SH-Λw = trans (front _ SH-Hg)
                  (trans (X₂.⟪⟫-≈ (sym sp) (X₂.⟪⟫-•₂ cw refl) (X₂.⟪⟫-•₂ refl cw))
                         (back _ (sym SH-Hg)))
      where
      cH : Circuit N
      cH = (X • ε) ↑ ↑ • Hg (₂₊ k) • (X • ε) ↑ ↑
      sp : Λ • cH ≈ cH • Λ
      sp = Eq.subst (λ z → Λ • ((X • z ↑) ↑ ↑ • Hg (₂₊ k) • (X • z ↑) ↑ ↑) ≈
                           ((X • z ↑) ↑ ↑ • Hg (₂₊ k) • (X • z ↑) ↑ ↑) • Λ)
                    (allT (₂₊ k)) (sep k below (replicate (₂₊ k) true))
      cw : X₂.⟪ cH ⟫ ≈ Hg (₂₊ k)
      cw = trans (X₂.⟪⟫-cong (cong right-unit (back _ right-unit))) (X₂.⟪⟫-⟪⟫ (Hg (₂₊ k)))

    SH-B₂₁ : SH • B₂₁ ≈ B₂₁ • SH
    SH-B₂₁ = trans (back _ B₂₁-form) (trans (pass₂ SH-Λ SH-Λw) (front _ (sym B₂₁-form)))

    -- Y letter by letter.
    SH-Y : SH • ΛXZ (₃₊ k) ↑ ≈ ΛXZ (₃₊ k) ↑ • SH
    SH-Y = pass₂ SH-B₂₁ (pass₂ SH-CH (pass₂ SH-B₂₁ SH-CH))

  ----------------------------------------------------------------------
  -- The canonical form of rule (44)

  core44 : SH • C k below ≈ C k below • SH
  core44 = trans (back _ (eq361 k below)) (trans (pass₂ SH-Λ SH-Y) (front _ (sym (eq361 k below))))
