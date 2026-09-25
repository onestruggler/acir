------------------------------------------------------------------------
-- Presentations of groups
--
-- A black and a white control merge (Clément, Lemma D.8, Equations
-- (301) and (302))
--
-- The box on wire 0 with its control on wire 2 black, times the same
-- with that control white, is the box without it: B₀₁, wire 2 idle.
-- The paper's proof (checked numerically first, scratchpad t301.py):
-- write the first box in its B-form W B V B, (269), and the second in
-- its form B W B V, (300), under X on wire 2 (which the smaller box B
-- does not see); B B cancels one width down; on three wires V W° is
-- CZ ↑ • ZX₁ (ZX₁ the singly controlled ZX on wire 0 from wire 1), the
-- CZ passes to the end (for B it is (272)); between W and the rest
-- ZX₁ XZ₁ = ε is inserted, and XZ₁ B ZX₁ B is the box B₀₁ — (305) one
-- width down with wire 2 idle; that box passes ZX₁ ((304) one width
-- down) and W, (287); and what is left is ε on three wires.
--
-- (302), the two in the other order, is (301) under X on wire 2, which
-- passes B₀₁: the cycle of place 2 carries it to wire 0, idle there.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.BoxMerge
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Integer using (+_ ; -[1+_])
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj ; ax)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Blocks complete₂ using (L-sem)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃ using (L₃-sem)
open import Examples.Groups.Real-Clifford+CH.Semantics using (Mat ; mat ; _+√2_ ; mulM ; scaleM ; √2^_)
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧M ; len)
open import Examples.Groups.Real-Clifford+CH.Soundness.Relators using (Same ; ≡-same)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Locals using (Wᴸ ; Wᴸ-def ; Vᴸ ; Vᴸ-def)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Locals2 using (ZX₀₁ᴸ ; ZX₀₁ᴸ-def)
open import Examples.Groups.Real-Clifford+CH.Evaluation using (by-rows)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Sem using (B□)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SemZX using (B₁₀)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SemMerge using (ZX₀ ; XZ₀ ; sem-305 ; sem-304)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place
  using (place ; place-• ; place-low ; lemma-5-1 ; cyc ; cyc⁻¹)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZXPass complete₂ complete₃ using (Complete)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Keystone complete₂ complete₃
  using (B□-CZ↑ ; B□² ; place-B□ ; commute-placed)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxZX complete₂ complete₃ using (B₀₁ ; eq287)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxMore complete₂ complete₃ using (eq300)

-- (301), (302): the black and the white control on wire 2 merge, in
-- either order.
Eq301 Eq302 : ℕ → Set
Eq301 k = (₄₊ k) ⊢ Λ□ (₃₊ k) • (X ↑ ↑ • Λ□ (₃₊ k) • X ↑ ↑) ≈ B₀₁ k
Eq302 k = (₄₊ k) ⊢ (X ↑ ↑ • Λ□ (₃₊ k) • X ↑ ↑) • Λ□ (₃₊ k) ≈ B₀₁ k

module _ (k : ℕ) (complete : Complete k) where

  private
    open Tools ((₄₊ k) VRel,_===_)

    Λ W V B Λ↑ ZX₁ XZ₁ : Circuit (₄₊ k)
    Λ   = Λ□ (₃₊ k)
    W   = CCZX
    V   = CCXZ
    B   = B□ k
    Λ↑  = Λ□ (₂₊ k) ↑
    ZX₁ = ΛZX 1 ↓ᵏ (₂₊ k)
    XZ₁ = ΛXZ 1 ↓ᵏ (₂₊ k)

    X₂² : (₄₊ k) ⊢ X ↑ ↑ • X ↑ ↑ ≈ ε
    X₂² = L₃-sem (X ↑ ↑ • X ↑ ↑) ε Eq.refl

    module C₂ = Conj {₄₊ k} (X ↑ ↑) X₂²

    W° V° : Circuit (₄₊ k)
    W° = C₂.⟪ W ⟫
    V° = C₂.⟪ V ⟫

    ------------------------------------------------------------------
    -- X on wire 2 passes B, which does not see it

    X₂-τ : (₄₊ k) ⊢ X ↑ ↑ • τ₀₂ ≈ τ₀₂ • X ↓
    X₂-τ = L₃-sem (X ↑ ↑ • τ₀₂) (τ₀₂ • X) Eq.refl

    τ-X₂ : (₄₊ k) ⊢ τ₀₂ • X ↑ ↑ ≈ X ↓ • τ₀₂
    τ-X₂ = L₃-sem (τ₀₂ • X ↑ ↑) (X • τ₀₂) Eq.refl

    X₀-Λ↑ : (₄₊ k) ⊢ X ↓ • Λ↑ • X ↓ ≈ Λ↑
    X₀-Λ↑ = begin
      (H • Z • H) • Λ↑ • (H • Z • H)
        ≈⟨ by-passoc ((□ • □ • □) • □ • (□ • □ • □)) (□ • □ • (□ • □) • □ • □ • □) Eq.refl ⟩
      H • Z • (H • Λ↑) • H • Z • H
        ≈⟨ back _ (back _ (front _ (sym (comm-gate₁-w↑ H-gate (Λ□ (₂₊ k)))))) ⟩
      H • Z • (Λ↑ • H) • H • Z • H
        ≈⟨ by-passoc (□ • □ • (□ • □) • □ • □ • □) (□ • (□ • □) • (□ • □) • □ • □) Eq.refl ⟩
      H • (Z • Λ↑) • (H • H) • Z • H
        ≈⟨ back _ (cong (sym (comm-gate₁-w↑ Z-gate (Λ□ (₂₊ k)))) (front _ (ax order-H))) ⟩
      H • (Λ↑ • Z) • ε • Z • H
        ≈⟨ back _ (back _ left-unit) ⟩
      H • (Λ↑ • Z) • Z • H
        ≈⟨ by-passoc (□ • (□ • □) • □ • □) ((□ • □) • (□ • □) • □) Eq.refl ⟩
      (H • Λ↑) • (Z • Z) • H
        ≈⟨ cong (sym (comm-gate₁-w↑ H-gate (Λ□ (₂₊ k)))) (front _ (ax order-Z)) ⟩
      (Λ↑ • H) • ε • H
        ≈⟨ back _ left-unit ⟩
      (Λ↑ • H) • H
        ≈⟨ cancelʳ _ (ax order-H) ⟩
      Λ↑ ∎

    X₂-B : (₄₊ k) ⊢ C₂.⟪ B ⟫ ≈ B
    X₂-B = begin
      X ↑ ↑ • (τ₀₂ • Λ↑ • τ₀₂) • X ↑ ↑     ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (X ↑ ↑ • τ₀₂) • Λ↑ • (τ₀₂ • X ↑ ↑)   ≈⟨ cong X₂-τ (back _ τ-X₂) ⟩
      (τ₀₂ • X ↓) • Λ↑ • (X ↓ • τ₀₂)       ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
      τ₀₂ • (X ↓ • Λ↑ • X ↓) • τ₀₂         ≈⟨ back _ (front _ X₀-Λ↑) ⟩
      τ₀₂ • Λ↑ • τ₀₂ ∎

    ------------------------------------------------------------------
    -- Three and two wires

    -- Stored-matrix equalities through the literals of Locals.
    lit-same : ∀ {u v : Circuit 3} {Mu Mv : Mat 3} → ⟦ u ⟧M ≡ Mu → ⟦ v ⟧M ≡ Mv →
               scaleM (√2^ len v) Mu ≡ scaleM (√2^ len u) Mv → Same u v
    lit-same {u} {v} eu ev e = ≡-same u v (Eq.trans (Eq.cong (scaleM _) eu) (Eq.trans e (Eq.cong (scaleM _) (Eq.sym ev))))

    -- The readings of the one-gate factors, named so that no implicit
    -- of the products is left to be solved by evaluation.
    X₂M CZ₁₂M : Mat 3
    X₂M   = ⟦ X {0} ↑ ↑ ⟧M
    CZ₁₂M = ⟦ CZ {0} ↑ ⟧M

    rX₂ : ⟦ X {0} ↑ ↑ ⟧M ≡ X₂M
    rX₂ = Eq.refl

    rCZ : ⟦ CZ {0} ↑ ⟧M ≡ CZ₁₂M
    rCZ = Eq.refl

    -- V negated on wire 2, as a literal.
    V°ᴸ : Mat 3
    V°ᴸ = mat ((((((((+ 8388608) +√2 (+ 0)) , ((+ 0) +√2 (+ 0))) , (((+ 0) +√2 (+ 0)) , ((+ 0) +√2 (+ 0)))) , ((((+ 0) +√2 (+ 0)) , ((+ 0) +√2 (+ 0))) , (((+ 0) +√2 (+ 0)) , ((+ 0) +√2 (+ 0))))) , (((((+ 0) +√2 (+ 0)) , ((+ 8388608) +√2 (+ 0))) , (((+ 0) +√2 (+ 0)) , ((+ 0) +√2 (+ 0)))) , ((((+ 0) +√2 (+ 0)) , ((+ 0) +√2 (+ 0))) , (((+ 0) +√2 (+ 0)) , ((+ 0) +√2 (+ 0)))))) , ((((((+ 0) +√2 (+ 0)) , ((+ 0) +√2 (+ 0))) , (((+ 0) +√2 (+ 0)) , ((+ 0) +√2 (+ 0)))) , ((((+ 0) +√2 (+ 0)) , ((+ 0) +√2 (+ 0))) , (((+ 8388608) +√2 (+ 0)) , ((+ 0) +√2 (+ 0))))) , (((((+ 0) +√2 (+ 0)) , ((+ 0) +√2 (+ 0))) , (((+ 0) +√2 (+ 0)) , ((+ 8388608) +√2 (+ 0)))) , ((((+ 0) +√2 (+ 0)) , ((+ 0) +√2 (+ 0))) , (((+ 0) +√2 (+ 0)) , ((+ 0) +√2 (+ 0))))))) , (((((((+ 0) +√2 (+ 0)) , ((+ 0) +√2 (+ 0))) , (((+ 0) +√2 (+ 0)) , ((+ 0) +√2 (+ 0)))) , ((((+ 8388608) +√2 (+ 0)) , ((+ 0) +√2 (+ 0))) , (((+ 0) +√2 (+ 0)) , ((+ 0) +√2 (+ 0))))) , (((((+ 0) +√2 (+ 0)) , ((+ 0) +√2 (+ 0))) , (((+ 0) +√2 (+ 0)) , ((+ 0) +√2 (+ 0)))) , ((((+ 0) +√2 (+ 0)) , ((+ 8388608) +√2 (+ 0))) , (((+ 0) +√2 (+ 0)) , ((+ 0) +√2 (+ 0)))))) , ((((((+ 0) +√2 (+ 0)) , ((+ 0) +√2 (+ 0))) , (((-[1+ 8388607 ]) +√2 (+ 0)) , ((+ 0) +√2 (+ 0)))) , ((((+ 0) +√2 (+ 0)) , ((+ 0) +√2 (+ 0))) , (((+ 0) +√2 (+ 0)) , ((+ 0) +√2 (+ 0))))) , (((((+ 0) +√2 (+ 0)) , ((+ 0) +√2 (+ 0))) , (((+ 0) +√2 (+ 0)) , ((+ 0) +√2 (+ 0)))) , ((((+ 0) +√2 (+ 0)) , ((+ 0) +√2 (+ 0))) , (((+ 0) +√2 (+ 0)) , ((+ 8388608) +√2 (+ 0))))))))

    V°ᴸ-def : ⟦ X {0} ↑ ↑ • CCXZ {0} • X {0} ↑ ↑ ⟧M ≡ V°ᴸ
    V°ᴸ-def = by-rows (X {0} ↑ ↑ • CCXZ {0} • X {0} ↑ ↑) Eq.refl

    VW° : (₄₊ k) ⊢ V • W° ≈ CZ ↑ • ZX₁
    VW° = L₃-sem (CCXZ • (X ↑ ↑ • CCZX • X ↑ ↑)) (CZ ↑ • (ΛZX 1 ↓ᵏ 1))
            Eq.refl

    CZ-ZX : (₄₊ k) ⊢ CZ ↑ • ZX₁ ≈ ZX₁ • CZ ↑
    CZ-ZX = L₃-sem (CZ ↑ • (ΛZX 1 ↓ᵏ 1)) ((ΛZX 1 ↓ᵏ 1) • CZ ↑)
              Eq.refl

    CZ-V° : (₄₊ k) ⊢ CZ ↑ • V° ≈ V° • CZ ↑
    CZ-V° = L₃-sem (CZ ↑ • (X ↑ ↑ • CCXZ • X ↑ ↑)) ((X ↑ ↑ • CCXZ • X ↑ ↑) • CZ ↑)
              Eq.refl

    rest : (₄₊ k) ⊢ W • ZX₁ • V° • CZ ↑ ≈ ε
    rest = L₃-sem (CCZX • (ΛZX 1 ↓ᵏ 1) • (X ↑ ↑ • CCXZ • X ↑ ↑) • CZ ↑) ε
             Eq.refl

    ZX-XZ : (₄₊ k) ⊢ ZX₁ • XZ₁ ≈ ε
    ZX-XZ = L-sem (ΛZX 1 • ΛXZ 1) ε Eq.refl

    ------------------------------------------------------------------
    -- One width down, with wire 2 idle

    place-ZX : (₄₊ k) ⊢ place 2 (ZX₀ k) ≈ ZX₁
    place-ZX = place-low 2 (ΛZX 1)

    place-XZ : (₄₊ k) ⊢ place 2 (XZ₀ k) ≈ XZ₁
    place-XZ = place-low 2 (ΛXZ 1)

    e305 : (₄₊ k) ⊢ XZ₁ • B • ZX₁ • B ≈ B₀₁ k
    e305 = begin
      XZ₁ • B • ZX₁ • B
        ≈⟨ cong (sym place-XZ) (cong (sym (place-B□ k complete)) (cong (sym place-ZX) (sym (place-B□ k complete)))) ⟩
      place 2 (XZ₀ k) • place 2 (B₁₀ k) • place 2 (ZX₀ k) • place 2 (B₁₀ k)
        ≈⟨ back _ (back _ (sym (place-• 2 (ZX₀ k) (B₁₀ k)))) ⟩
      place 2 (XZ₀ k) • place 2 (B₁₀ k) • place 2 (ZX₀ k • B₁₀ k)
        ≈⟨ back _ (sym (place-• 2 (B₁₀ k) (ZX₀ k • B₁₀ k))) ⟩
      place 2 (XZ₀ k) • place 2 (B₁₀ k • ZX₀ k • B₁₀ k)
        ≈⟨ sym (place-• 2 (XZ₀ k) (B₁₀ k • ZX₀ k • B₁₀ k)) ⟩
      place 2 (XZ₀ k • B₁₀ k • ZX₀ k • B₁₀ k)
        ≈⟨ lemma-5-1 2 complete (sem-305 k) ⟩
      place 2 (Λ□ (₂₊ k)) ∎

    ZX-B₀₁ : (₄₊ k) ⊢ B₀₁ k • ZX₁ ≈ ZX₁ • B₀₁ k
    ZX-B₀₁ = commute-placed k complete {X = Λ□ (₂₊ k)} {Y = ZX₀ k} refl place-ZX (sem-304 k)

  ----------------------------------------------------------------------
  -- (301)

  eq301 : Eq301 k
  eq301 = begin
    Λ • C₂.⟪ Λ ⟫
      ≈⟨ back _ (trans (C₂.⟪⟫-cong (eq300 k complete)) (C₂.⟪⟫-•₄ X₂-B refl X₂-B refl)) ⟩
    (W • B • V • B) • (B • W° • B • V°)
      ≈⟨ by-passoc ((□ • □ • □ • □) • (□ • □ • □ • □)) (□ • □ • □ • (□ • □) • □ • □ • □) Eq.refl ⟩
    W • B • V • (B • B) • W° • B • V°
      ≈⟨ back _ (back _ (back _ (trans (front _ (B□² k complete)) left-unit))) ⟩
    W • B • V • W° • B • V°
      ≈⟨ back _ (back _ (sym assoc)) ⟩
    W • B • (V • W°) • B • V°
      ≈⟨ back _ (back _ (front _ VW°)) ⟩
    W • B • (CZ ↑ • ZX₁) • B • V°
      ≈⟨ back _ (back _ (begin
           (CZ ↑ • ZX₁) • B • V°        ≈⟨ front _ CZ-ZX ⟩
           (ZX₁ • CZ ↑) • B • V°        ≈⟨ by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
           ZX₁ • (CZ ↑ • B) • V°        ≈⟨ back _ (front _ (sym (B□-CZ↑ k complete))) ⟩
           ZX₁ • (B • CZ ↑) • V°        ≈⟨ back _ assoc ⟩
           ZX₁ • B • (CZ ↑ • V°)        ≈⟨ back _ (back _ CZ-V°) ⟩
           ZX₁ • B • (V° • CZ ↑) ∎)) ⟩
    W • B • ZX₁ • B • (V° • CZ ↑)
      ≈⟨ back _ (sym (trans (front _ ZX-XZ) left-unit)) ⟩
    W • (ZX₁ • XZ₁) • B • ZX₁ • B • (V° • CZ ↑)
      ≈⟨ by-passoc (□ • (□ • □) • □ • □ • □ • □) (□ • □ • (□ • □ • □ • □) • □) Eq.refl ⟩
    W • ZX₁ • (XZ₁ • B • ZX₁ • B) • (V° • CZ ↑)
      ≈⟨ back _ (back _ (front _ e305)) ⟩
    W • ZX₁ • B₀₁ k • (V° • CZ ↑)
      ≈⟨ back _ (by-passoc (□ • □ • □) ((□ • □) • □) Eq.refl) ⟩
    W • (ZX₁ • B₀₁ k) • (V° • CZ ↑)
      ≈⟨ back _ (front _ (sym ZX-B₀₁)) ⟩
    W • (B₀₁ k • ZX₁) • (V° • CZ ↑)
      ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
    (W • B₀₁ k) • ZX₁ • (V° • CZ ↑)
      ≈⟨ front _ (sym (eq287 k complete)) ⟩
    (B₀₁ k • W) • ZX₁ • (V° • CZ ↑)
      ≈⟨ trans assoc (back _ (trans (back _ (back _ refl)) rest)) ⟩
    B₀₁ k • ε
      ≈⟨ right-unit ⟩
    B₀₁ k ∎

  ----------------------------------------------------------------------
  -- (302): (301) under X on wire 2, which B₀₁ does not see

  private
    X₂-cyc⁻¹ : (₄₊ k) ⊢ X ↑ ↑ • cyc⁻¹ 2 ≈ cyc⁻¹ 2 • X ↓
    X₂-cyc⁻¹ = L₃-sem (X ↑ ↑ • cyc⁻¹ 2) (cyc⁻¹ 2 • X) Eq.refl

    cyc-X₂ : (₄₊ k) ⊢ cyc 2 • X ↑ ↑ ≈ X ↓ • cyc 2
    cyc-X₂ = L₃-sem (cyc 2 • X ↑ ↑) (X • cyc 2) Eq.refl

    X₂-B₀₁ : (₄₊ k) ⊢ C₂.⟪ B₀₁ k ⟫ ≈ B₀₁ k
    X₂-B₀₁ = begin
      X ↑ ↑ • (cyc⁻¹ 2 • Λ↑ • cyc 2) • X ↑ ↑
        ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (X ↑ ↑ • cyc⁻¹ 2) • Λ↑ • (cyc 2 • X ↑ ↑)
        ≈⟨ cong X₂-cyc⁻¹ (back _ cyc-X₂) ⟩
      (cyc⁻¹ 2 • X ↓) • Λ↑ • (X ↓ • cyc 2)
        ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
      cyc⁻¹ 2 • (X ↓ • Λ↑ • X ↓) • cyc 2
        ≈⟨ back _ (front _ X₀-Λ↑) ⟩
      cyc⁻¹ 2 • Λ↑ • cyc 2 ∎

  eq302 : Eq302 k
  eq302 = begin
    C₂.⟪ Λ ⟫ • Λ              ≈⟨ back _ (sym (C₂.⟪⟫-⟪⟫ Λ)) ⟩
    C₂.⟪ Λ ⟫ • C₂.⟪ C₂.⟪ Λ ⟫ ⟫ ≈⟨ sym (C₂.⟪⟫-• Λ C₂.⟪ Λ ⟫) ⟩
    C₂.⟪ Λ • C₂.⟪ Λ ⟫ ⟫        ≈⟨ C₂.⟪⟫-cong eq301 ⟩
    C₂.⟪ B₀₁ k ⟫               ≈⟨ X₂-B₀₁ ⟩
    B₀₁ k ∎
