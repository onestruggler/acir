------------------------------------------------------------------------
-- Presentations of groups
--
-- The core of rule (45) on four qubits (Clément, Appendix E.5 at n = 4,
-- from Lemma D.5)
--
-- Canon45Gen's argument — the three-qubit proof of (146) with multiple
-- controls — at width four.  Its inputs: the box facts from canon4, the
-- swap of the wires 1 2 on the box ((157)), the box against its copies
-- white on wire 1 (the merge of canon4 and its X-conjugate) and on wire 2
-- ((170), (170′)), against the box on wire 1 white on wire 2 ((179)
-- under the lower swap), and P ⊗ P passing the CZ of the wires 2 3; the
-- H gate is ΛH₀₁ itself, the box on wire 1 between P ⊗ P, with (338) for
-- x = y (W4.Cores), (194) under X on wire 2, X on its box wire ((207)
-- under the lower swap) and (333) as (210) under the swaps.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.Lemma88.W4.Core45
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂ using (module N₁ ; module N₂)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
  using (module S₀₁ ; module S₁₂ ; L-sem)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃ using (box₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Box complete₂ complete₃ using (eq157)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Controlled complete₂ complete₃ using (°box₃ ; eq170 ; eq170′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours complete₂ complete₃ using (eq179)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours2 complete₂ complete₃ using (N₂-box₃′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours3 complete₂ complete₃ using (eq194)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates complete₂ complete₃ using (ΛH₀₁-PP)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates2 complete₂ complete₃ using (eq207)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃ using (ZX₃-form₄ ; S₁₂-ZX₃)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (low-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon4 complete₂ complete₃ using (canon4)
import Examples.Groups.Real-Clifford+CH.GeneralN.Canon45Gen complete₂ complete₃ as G45
open import Examples.Groups.Real-Clifford+CH.Lemma88.W4.Cores complete₂ complete₃ using (HG-box₃)

open Tools (4 VRel,_===_)

private
  HG : Circuit 4
  HG = Ex ↓ • ΛH 2 • Ex ↓

  sX : S₀₁.⟪ X ⟫ ≈ X ↑
  sX = L-sem (Ex • X • Ex) (X ↑) Eq.refl

  -- X on the box wire passes HG ((207)).
  X-Hg : X ↑ • HG ≈ HG • X ↑
  X-Hg = S₀₁.⟪⟫-≈ eq207 (S₀₁.⟪⟫-•₂ sX refl) (S₀₁.⟪⟫-•₂ refl sX)

  -- The box passes its copy white on wire 1: both products are the merge.
  Λ-Zc : box₃ • (X ↑ • box₃ • X ↑) ≈ (X ↑ • box₃ • X ↑) • box₃
  Λ-Zc = trans merge (sym zm)
    where
    merge : box₃ • (X ↑ • box₃ • X ↑) ≈ CZ ↑ ↑
    merge = Canon.merge canon4
    xm : X ↑ • CZ ↑ ↑ ≈ CZ ↑ ↑ • X ↑
    xm = lemma-cong↑ (X • CZ ↑) (CZ ↑ • X) (X-↑ CZ)
    zm : (X ↑ • box₃ • X ↑) • box₃ ≈ CZ ↑ ↑
    zm = N₁.⟪⟫-≈ merge (trans (N₁.⟪⟫-• box₃ (X ↑ • box₃ • X ↑)) (back _ (N₁.⟪⟫-⟪⟫ box₃))) (N₁.⟪⟫-fix xm)

  PP-M : PP ↓ • CZ ↑ ↑ ≈ CZ ↑ ↑ • PP ↓
  PP-M = low-comm PP CZ

  -- (338) with the colourings differing on wire 2: (194) under X there.
  sepΛ : box₃ • (X ↑ ↑ • HG • X ↑ ↑) ≈ (X ↑ ↑ • HG • X ↑ ↑) • box₃
  sepΛ = N₂.⟪⟫-≈ (sym eq194) (N₂.⟪⟫-•₂ (N₂.⟪⟫-⟪⟫ box₃) refl) (N₂.⟪⟫-•₂ refl (N₂.⟪⟫-⟪⟫ box₃))

  -- The box against the box on wire 1 white on wire 2: (179) under the
  -- lower swap.
  c336′ : box₃ • (X ↑ ↑ • (Ex ↓ • box₃ • Ex ↓) • X ↑ ↑) ≈ (X ↑ ↑ • (Ex ↓ • box₃ • Ex ↓) • X ↑ ↑) • box₃
  c336′ = S₀₁.⟪⟫-≈ eq179 (S₀₁.⟪⟫-•₂ (S₀₁.⟪⟫-⟪⟫ box₃) (sym N₂-box₃′)) (S₀₁.⟪⟫-•₂ (sym N₂-box₃′) (S₀₁.⟪⟫-⟪⟫ box₃))

  -- The box against its copy white on wire 2: both products are (170).
  c335′ : box₃ • °box₃ ≈ °box₃ • box₃
  c335′ = trans eq170 (sym eq170′)

  -- (333): HG and the box on wire 2 make ΛZX, (210) under the swaps.
  eq333 : HG • S₁₂.⟪ Ex ↓ • box₃ • Ex ↓ ⟫ • HG • S₁₂.⟪ Ex ↓ • box₃ • Ex ↓ ⟫ ≈ ΛZX 3
  eq333 = trans (sym (S₁₂.⟪⟫-•₄ (S₁₂.⟪⟫-⟪⟫ HG) refl (S₁₂.⟪⟫-⟪⟫ HG) refl))
                (trans (S₁₂.⟪⟫-cong (sym ZX₃-form₄)) S₁₂-ZX₃)

core45₁ : ΛH 2 • (X ↑ • Λ□ 3 • X ↑) •
            ((X ↑ • X ↑ ↑) • (Ex ↑ • Ex ↓) • ΛH 2 • (Ex ↓ • Ex ↑) • (X ↑ • X ↑ ↑)) •
            ΛH 2 •
            ((X ↑ • X ↑ ↑) • (Ex ↑ • Ex ↓) • ΛH 2 • (Ex ↓ • Ex ↑) • (X ↑ • X ↑ ↑))
        ≈ ((X ↑ • X ↑ ↑) • (Ex ↑ • Ex ↓) • ΛH 2 • (Ex ↓ • Ex ↑) • (X ↑ • X ↑ ↑)) •
            ΛH 2 •
            ((X ↑ • X ↑ ↑) • (Ex ↑ • Ex ↓) • ΛH 2 • (Ex ↓ • Ex ↑) • (X ↑ • X ↑ ↑)) •
            (X ↑ • Λ□ 3 • X ↑) • ΛH 2
core45₁ = G45.core45 {0} canon4 HG ΛH₀₁-PP refl X-Hg (sym HG-box₃) eq157 Λ-Zc PP-M sepΛ c336′ c335′ eq333 S₁₂-ZX₃
