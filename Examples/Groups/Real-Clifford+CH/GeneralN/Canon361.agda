------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoded double exchange at the canonical position (Clément,
-- Lemma D.15, Equation (361))
--
-- At width 5 + k, conjugated by the negations of the wires 2 …, the
-- decoded X_[0,3] X_[1,2] of Definition 8.3 is
--
--   C = (Yb • B₁ • Λ) • (XW • (XB • Yb • ZXB) • XWi)
--
-- with XB, ZXB the rotations on wire 0, XW, XWi the same white on wire
-- 1, Yb the rotation on wire 1, B₁ the box on wire 1 and Λ the box on
-- wire 0.  (361) says C ≈ Λ • Y, with Y the rotation on wire 1 and wire
-- 0 idle (`eq361`).  (354) on wire 1 merges XW XB and ZXB XWi into the
-- rotation on wire 0 with wire 1 idle and its inverse, and these carry Yb
-- to its copy white on wire 0 (Lemma 8.5, RotConj).  Yb B₁ is Yb's
-- inverse ((355), (317)), which passes Λ and becomes Yb (Canon31.K1).
-- Yb and its white copy merge into Y ((354)).  Shared by the rules (43)
-- and (44).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.Canon361
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (true ; false)
open import Data.Nat using (ℕ ; s≤s ; z≤n)
open import Data.Vec using (_∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module S ; Ex² ; S-X↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (placeAt ; placeAt-place ; placeAt-step)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceCalc using (placeAt-zero)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃ using (Completes)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CanonN complete₂ complete₃ using (canonN)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX353 complete₂ complete₃ using (allT)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX355 complete₂ complete₃ using (eq355)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX354 complete₂ complete₃ using (eq354₁ ; eq354₁′)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon31 complete₂ complete₃ using (K1)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotConj complete₂ complete₃ using (l85)
import Examples.Groups.Real-Clifford+CH.Lemma88.Invol as Invol

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    N : ℕ
    N = ₁₊ (₄₊ k)

    completes : Completes (₁₊ k)
    completes j≤ = below (s≤s (s≤s (s≤s (s≤s j≤))))

    canon : Canon (₂₊ k)
    canon = canonN k completes

    module I = Invol canon complete₂

  open Tools (N VRel,_===_)

  -- The gates.
  Λ B₁ XB ZXB XW XWi Yb Ybi Y : Circuit N
  Λ   = Λ□ (₄₊ k)
  B₁  = Ex ↓ • Λ • Ex ↓
  XB  = ΛXZ (₄₊ k)
  ZXB = ΛZX (₄₊ k)
  XW  = X ↑ • XB • X ↑
  XWi = X ↑ • ZXB • X ↑
  Yb  = Ex ↓ • XB • Ex ↓
  Ybi = Ex ↓ • ZXB • Ex ↓
  Y   = ΛXZ (₃₊ k) ↑

  -- The decoded X_[0,3] X_[1,2], between the negations.
  C : Circuit N
  C = (Yb • B₁ • Λ) • (XW • (XB • Yb • ZXB) • XWi)

  private
    ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
    ≡→≈ Eq.refl = refl

    ones : Bits (₃₊ k)
    ones = replicate (₃₊ k) true

    -- The idle wire 1 of a placement is wire 0 under the swap.
    place-Y : ∀ (u : Circuit (₄₊ k)) → Ex • u ↑ • Ex ≈ placeAt 1 u
    place-Y u = sym (trans (placeAt-step 0 u (s≤s z≤n)) (back _ (front _ (placeAt-zero u))))

    -- The rotation on wire 0 with wire 1 idle, and its inverse.
    W Wi : Circuit N
    W  = Ex • Y • Ex
    Wi = Ex • ΛZX (₃₊ k) ↑ • Ex

    -- (354) on wire 1.
    XW-XB : XW • XB ≈ W
    XW-XB = trans (eq354₁ k below false)
                  (trans (≡→≈ (Eq.sym (placeAt-place 1 (ΛXZ (₃₊ k))))) (sym (place-Y (ΛXZ (₃₊ k)))))

    ZXB-XWi : ZXB • XWi ≈ Wi
    ZXB-XWi = trans (eq354₁′ k below true)
                    (trans (≡→≈ (Eq.sym (placeAt-place 1 (ΛZX (₃₊ k))))) (sym (place-Y (ΛZX (₃₊ k)))))

    -- Lemma 8.5, under the swap.
    W-Yb : W • Yb • Wi ≈ X • Yb • X
    W-Yb = S.⟪⟫-≈ (l85 k below false) (S.⟪⟫-•₃ refl refl refl) (S.⟪⟫-•₃ S-X↑ refl S-X↑)

    -- Yb and its copy white on wire 0 merge into Y ((354), under the swap).
    Yb-Yw : Yb • (X • Yb • X) ≈ Y
    Yb-Yw = S.⟪⟫-≈ (eq354₁′ k below false) (S.⟪⟫-•₂ refl (S.⟪⟫-•₃ S-X↑ refl S-X↑))
                   (trans (S.⟪⟫-cong (≡→≈ (Eq.sym (placeAt-place 1 (ΛXZ (₃₊ k))))))
                          (conj-sym Ex² (place-Y (ΛXZ (₃₊ k)))))

    -- (355) and (317): XB Λ is ZXB, so Yb B₁ is Ybi.
    XB-Λ : XB • Λ ≈ ZXB
    XB-Λ = sym (begin
      ZXB                      ≈⟨ sym (trans (back _ (Canon.invol canon)) right-unit) ⟩
      ZXB • (Λ • Λ)            ≈⟨ back _ (front _ (eq355 k below)) ⟩
      ZXB • ((XB • XB) • Λ)    ≈⟨ by-passoc (□ • ((□ • □) • □)) ((□ • □) • (□ • □)) Eq.refl ⟩
      (ZXB • XB) • (XB • Λ)    ≈⟨ trans (front _ I.zx-xz) left-unit ⟩
      XB • Λ ∎)

    Yb-B₁ : Yb • B₁ ≈ Ybi
    Yb-B₁ = trans (sym (S.⟪⟫-• XB Λ)) (S.⟪⟫-cong XB-Λ)

    -- Canon31.K1, under the swap: Ybi passes Λ and becomes Yb.
    Ybi-Λ : Ybi • Λ ≈ Λ • Yb
    Ybi-Λ = S.⟪⟫-≈ K (S.⟪⟫-•₂ refl (S.⟪⟫-⟪⟫ Λ)) (S.⟪⟫-•₂ (S.⟪⟫-⟪⟫ Λ) refl)
      where
      eb : col (true ∷ true ∷ ones) B₁ ≈ B₁
      eb = trans (≡→≈ (Eq.cong (λ z → z • B₁ • z) (allT N))) (trans left-unit right-unit)
      K : ZXB • B₁ ≈ B₁ • XB
      K = trans (back _ (sym eb)) (trans (K1 k below true true true) (front _ eb))

  ----------------------------------------------------------------------
  -- (361)

  eq361 : C ≈ Λ • Y
  eq361 = begin
    (Yb • B₁ • Λ) • (XW • (XB • Yb • ZXB) • XWi)
      ≈⟨ back _ (by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl) ⟩
    (Yb • B₁ • Λ) • ((XW • XB) • Yb • (ZXB • XWi))
      ≈⟨ back _ (cong XW-XB (back _ ZXB-XWi)) ⟩
    (Yb • B₁ • Λ) • (W • Yb • Wi)
      ≈⟨ back _ W-Yb ⟩
    (Yb • B₁ • Λ) • (X • Yb • X)
      ≈⟨ front _ (trans (sym assoc) (front _ Yb-B₁)) ⟩
    (Ybi • Λ) • (X • Yb • X)
      ≈⟨ front _ Ybi-Λ ⟩
    (Λ • Yb) • (X • Yb • X)
      ≈⟨ trans assoc (back _ Yb-Yw) ⟩
    Λ • Y ∎
