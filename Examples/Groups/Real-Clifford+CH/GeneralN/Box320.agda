------------------------------------------------------------------------
-- Presentations of groups
--
-- The box as a product of rotations and smaller boxes (Clément, Lemma
-- D.12, Equations (318) and (320))
--
-- At width 5 + k, with the wires numbered from the bottom as D = 0,
-- C = 1, B = 2, A = 3 and the top wires 4 …: Kᵇ = S₀₁⟪ ZX₃ ⟫ is the
-- triply controlled ZX on wire 1 from the wires 0 2 3, and Box₃ the box
-- on wire 0 controlled by the wires 1 2 and the top wires, wire 3 idle.
--
-- (318): Kᵇ and its inverse pass Box₃ with its control on wire 2 white
-- and the one on wire 1 of either colour (`eq318`).  Gadget318 has it
-- with that control black; X on wire 1 carries it to the other colour,
-- turning the rotation on wire 1 over ((238) under the swap of the
-- wires 0 1), and the inverse follows.  The paper's remaining
-- parameters, the colours of the rotation's control on wire 3 and of
-- the box's top wires, are X on wires one of the two gates does not
-- use; they are left to the uses.
--
-- (320): the box is ZX₃ D₃ XZ₃ D₃ with D₃ = Kᵇ Box₃ Kᵇ⁻¹.  The paper's
-- proof: (295) is the same with the box C on wire 0 controlled by
-- wire 1 and the top wires in place of Box₃; C is Box₃ times Box₃
-- white on wire 2, G, in either order (Gadget319); Kᵇ and Kᵇ⁻¹ pass G
-- by (318) and XZ₃ passes it by (319), so the two G's meet around XZ₃
-- and cancel.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.Box320
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (n<1+n)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; X²)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂ using (module N₁ ; module N₂)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃ using (module S₀₁)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃
  using (ZX₃ ; XZ₃ ; eq208 ; eq208′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations5 complete₂ complete₃ using (eq238)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families2 complete₂ complete₃ using (rot)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families3 complete₂ complete₃ using (module N₀)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZXPass complete₂ complete₃ using (Complete)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (swapX ; swapX′ ; place-swap)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxForms complete₂ complete₃ using (C ; eq295)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Gadget318 complete₂ complete₃ using (Box₃ ; eq318₀)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Gadget319 complete₂ complete₃
  using (C′ ; bx ; eq319′ ; Box₃² ; G-C′ ; G-C′′)

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    N : ℕ
    N = ₁₊ (₄₊ k)

    complete : Complete (₁₊ k)
    complete = below (n<1+n (₄₊ k))

  open Tools (N VRel,_===_)
  open WordAlgebra (N VRel,_===_) using (comm-inv)

  -- The rotation on wire 1, and the box white on wire 2.
  Kᵇ Kᵇ′ G : Circuit N
  Kᵇ  = S₀₁.⟪ ZX₃ ⟫
  Kᵇ′ = S₀₁.⟪ XZ₃ ⟫
  G   = bx k true false

  private
    -- X on wire 1 through the swap of the wires 0 1 is X on wire 0.
    N₁-S₀₁ : ∀ w → N₁.⟪ S₀₁.⟪ w ⟫ ⟫ ≈ S₀₁.⟪ N₀.⟪ w ⟫ ⟫
    N₁-S₀₁ w = begin
      X ↑ • (Ex ↓ • w • Ex ↓) • X ↑
        ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (X ↑ • Ex ↓) • w • (Ex ↓ • X ↑)
        ≈⟨ cong swapX (back _ swapX′) ⟩
      (Ex ↓ • X ↓) • w • (X ↓ • Ex ↓)
        ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
      Ex ↓ • (X ↓ • w • X ↓) • Ex ↓ ∎

    -- X on the target turns the rotation over, (238).
    N₀-ZX₃ : N₀.⟪ ZX₃ ⟫ ≈ XZ₃
    N₀-ZX₃ = trans (sym assoc) (trans (front _ eq238) (cancelʳ _ X²))

    N₀-rot : ∀ a → N₀.⟪ rot (not a) ⟫ ≈ rot a
    N₀-rot false = N₀-ZX₃
    N₀-rot true  = trans (N₀.⟪⟫-cong (sym N₀-ZX₃)) (N₀.⟪⟫-⟪⟫ ZX₃)

    KK′ : Kᵇ • Kᵇ′ ≈ ε
    KK′ = trans (sym (S₀₁.⟪⟫-• ZX₃ XZ₃)) (trans (S₀₁.⟪⟫-cong eq208′) S₀₁.⟪⟫-ε)

    K′K : Kᵇ′ • Kᵇ ≈ ε
    K′K = trans (sym (S₀₁.⟪⟫-• XZ₃ ZX₃)) (trans (S₀₁.⟪⟫-cong eq208) S₀₁.⟪⟫-ε)

  ----------------------------------------------------------------------
  -- (318)

  private
    eq318• : ∀ a → S₀₁.⟪ rot a ⟫ • G ≈ G • S₀₁.⟪ rot a ⟫
    eq318• true  = eq318₀ k complete
    eq318• false = sym (comm-inv KK′ K′K (sym (eq318₀ k complete)))

  eq318 : ∀ a γ → S₀₁.⟪ rot a ⟫ • bx k γ false ≈ bx k γ false • S₀₁.⟪ rot a ⟫
  eq318 a true  = eq318• a
  eq318 a false = N₁.⟪⟫-≈ (eq318• (not a)) (N₁.⟪⟫-•₂ e refl) (N₁.⟪⟫-•₂ refl e)
    where
    e : N₁.⟪ S₀₁.⟪ rot (not a) ⟫ ⟫ ≈ S₀₁.⟪ rot a ⟫
    e = trans (N₁-S₀₁ (rot (not a))) (S₀₁.⟪⟫-cong (N₀-rot a))

  ----------------------------------------------------------------------
  -- (320)

  D₃ : Circuit N
  D₃ = Kᵇ • Box₃ k • Kᵇ′

  private
    G² : G • G ≈ ε
    G² = N₂.⟪⟫-invol (Box₃² k below)

    -- C is Box₃ times G, in either order.
    C-BG : C k ≈ Box₃ k • G
    C-BG = begin
      C k                        ≈⟨ place-swap (Λ□ (₂₊ k)) ⟩
      C′ k                       ≈⟨ sym (cancelˡ _ (Box₃² k below)) ⟩
      Box₃ k • Box₃ k • C′ k     ≈⟨ back _ (sym (G-C′′ k below)) ⟩
      Box₃ k • G ∎

    C-GB : C k ≈ G • Box₃ k
    C-GB = begin
      C k                        ≈⟨ place-swap (Λ□ (₂₊ k)) ⟩
      C′ k                       ≈⟨ sym (cancelʳ _ (Box₃² k below)) ⟩
      (C′ k • Box₃ k) • Box₃ k   ≈⟨ front _ (sym (G-C′ k below)) ⟩
      G • Box₃ k ∎

    D-l : Kᵇ • C k • Kᵇ′ ≈ D₃ • G
    D-l = begin
      Kᵇ • C k • Kᵇ′             ≈⟨ back _ (front _ C-BG) ⟩
      Kᵇ • (Box₃ k • G) • Kᵇ′    ≈⟨ back _ assoc ⟩
      Kᵇ • Box₃ k • G • Kᵇ′      ≈⟨ back _ (back _ (sym (eq318 false true))) ⟩
      Kᵇ • Box₃ k • Kᵇ′ • G      ≈⟨ by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl ⟩
      D₃ • G ∎

    D-r : Kᵇ • C k • Kᵇ′ ≈ G • D₃
    D-r = begin
      Kᵇ • C k • Kᵇ′             ≈⟨ back _ (front _ C-GB) ⟩
      Kᵇ • (G • Box₃ k) • Kᵇ′    ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
      (Kᵇ • G) • Box₃ k • Kᵇ′    ≈⟨ front _ (eq318 true true) ⟩
      (G • Kᵇ) • Box₃ k • Kᵇ′    ≈⟨ assoc ⟩
      G • D₃ ∎

    GXG : G • XZ₃ • G ≈ XZ₃
    GXG = begin
      G • XZ₃ • G      ≈⟨ sym assoc ⟩
      (G • XZ₃) • G    ≈⟨ front _ (sym (eq319′ k below true false)) ⟩
      (XZ₃ • G) • G    ≈⟨ cancelʳ _ G² ⟩
      XZ₃ ∎

  eq320 : Λ□ (₄₊ k) ≈ ZX₃ • D₃ • XZ₃ • D₃
  eq320 = begin
    Λ□ (₄₊ k)
      ≈⟨ eq295 k complete ⟩
    ZX₃ • (Kᵇ • C k • Kᵇ′) • XZ₃ • (Kᵇ • C k • Kᵇ′)
      ≈⟨ back _ (cong D-l (back _ D-r)) ⟩
    ZX₃ • (D₃ • G) • XZ₃ • (G • D₃)
      ≈⟨ by-passoc (□ • (□ • □) • □ • (□ • □)) (□ • □ • (□ • □ • □) • □) Eq.refl ⟩
    ZX₃ • D₃ • (G • XZ₃ • G) • D₃
      ≈⟨ back _ (back _ (front _ GXG)) ⟩
    ZX₃ • D₃ • XZ₃ • D₃ ∎
