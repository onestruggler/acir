------------------------------------------------------------------------
-- Presentations of groups
--
-- The box in its symmetric form, and the swap of its controls on the
-- wires 2 3 (Clément, Lemma D.8, Equations (292)–(295), (305), (306),
-- and Lemma D.13, Equation (336) with its controls black)
--
-- At width 5 + k, with the gates on the wires 0–3 spelled as in
-- FourQubit: K = ZX(1; 0, °2, 3), Kᵇ = ZX(1; 0, 2, 3), A = ZX(1; 0, 3),
-- ZX₃ = ZX(0; 1, 2, 3), and C the box on wire 0 controlled by wire 1
-- and the wires 4 … (the wires 2 3 idle).
--
-- (292): CCZX passes the box on wire 1 with its control on wire 2
-- white: in the B-form (269) under X on wire 2 and the swap of the wires
-- 0 1 its factors are ZX(1; 0, °2), the box C₃ on wire 0 with wire 2
-- idle, and XZ(1; 0, °2) — (139), (287), (140).
--
-- (293): K passes the box.  It passes each factor of the B-form (269):
-- CCZX and CCXZ by (216), (217), and B by (291) under the swap of the
-- wires 0 1 and X on wire 2 (which B, idle there, does not see).
--
-- (294): the box is CCZX A C A⁻¹ CCXZ A C A⁻¹ — (269) with its box B
-- written A C A⁻¹ C and C A C A⁻¹, both (269) one width down with wire
-- 2 idle; the C in the middle passes CCXZ one width down with wire 3
-- idle.
--
-- (295): the box is ZX₃ D XZ₃ D with D = Kᵇ C Kᵇ⁻¹, the paper's proof:
-- K⁻¹ K in front, K through the box by (293), the form (294), K⁻¹
-- through CCZX by (218), merged with A into Kᵇ by (225)/(226) and
-- (221)/(222) with (217) and (209) in the middle; then CCZX is ZX₃ times
-- ZX₃ white on wire 3, (223), which passes D — Kᵇ by (240) under X on
-- wire 2 and the swap of the wires 2 3, C by (290) under X on wire 3 —
-- and cancels against the XZ₃ white on wire 3 in CCXZ, (224).
--
-- (306): the swap of the wires 2 3 fixes every factor of (295): ZX₃ and
-- XZ₃ by (214), Kᵇ likewise, and C, idle on both wires.
--
-- (305): the box is XZ₀ B₁₀ ZX₀ B₁₀, B₁₀ the box with its box wire on
-- wire 1 and ZX₀ the singly controlled ZX on wire 0.  The paper's proof:
-- ZX₀ and XZ₀ are the merges of their doubly controlled versions on the
-- colour of wire 2, (136) and (138); the white ones pass B₁₀ ((292)
-- under X on wire 2) and cancel; D D = ε for D the box B₁₀ white on wire
-- 2, (299); CCZX passes D, (292); and B₁₀ D and D B₁₀ are B□, (301) and
-- (302) under the swap of the wires 0 1 — leaving the mirrored B-form,
-- (286).
--
-- (336), all controls black: the box and B₁₀ commute.  From the merges,
-- B₁₀ = B D = D B and D passes B; D passes CCZX and CCXZ, (292); so
-- Λ B₁₀ = W B V (B B₁₀) = W B V D = D W B V = (B₁₀ B) W B V = B₁₀ Λ,
-- the last step the B-form (300).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.BoxForms
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (true)
open import Data.Fin using (zero ; suc)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; Ex²)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Blocks complete₂ using (L-sem)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (module N₂ ; °CZXC ; °CXZC ; eq117 ; eq118 ; eq136 ; eq138 ; eq139 ; eq140)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
  using (module S₀₁ ; module S₂₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours complete₂ complete₃ using (module N₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃
  using (ZX₃ ; XZ₃ ; eq208 ; eq208′ ; eq209 ; eq214 ; eq214′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Crossed complete₂ complete₃
  using (K ; K′ ; K-K′ ; eq216 ; eq217 ; eq218)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Merges complete₂ complete₃
  using (Kᵇ ; Kᵇ′ ; CCZX₁₃ ; CCXZ₁₃ ; eq221 ; eq222 ; eq223′ ; eq224 ; eq225 ; eq226)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families3 complete₂ complete₃ using (eq240)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra
open import Examples.Groups.Real-Clifford+CH.GeneralN.Sem using (B□)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SemZX using (B₁₀)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SemBoxes using (C₀ ; sem-294a ; sem-294b ; sem-294c ; sem-C₀-yB)
open import Examples.Groups.Real-Clifford+CH.TopWeakening using (top)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place
open import Examples.Groups.Real-Clifford+CH.GeneralN.Networks using (scyc ; scyc⁻¹)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (perm-≈)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle
  using (place-yB ; place-swap ; swap-idle₂₃ ; X-place)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZXPass complete₂ complete₃ using (Complete)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Keystone complete₂ complete₃ using (place-B□)
open import Examples.Groups.Real-Clifford+CH.GeneralN.TwoBoxes complete₂ complete₃
  using (eq290 ; eq291 ; B₁₀↑-place)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxZX complete₂ complete₃ using (eq287)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box complete₂ complete₃ using (eq286)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFull complete₂ complete₃ using (eq299)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxMerge complete₂ complete₃ using (eq301 ; eq302)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxMore complete₂ complete₃ using (eq300)

-- The box on wire 0 controlled by wire 1 and the wires 4 …, the wires
-- 2 3 idle.
C : ∀ k → Circuit (₁₊ (₄₊ k))
C k = place 2 (C₀ k)

Eq292 Eq293 Eq294 Eq295 Eq305 Eq306 Eq336 : ℕ → Set
Eq292 k = (₁₊ (₄₊ k)) ⊢ CCZX • S₀₁.⟪ N₂.⟪ Λ□ (₄₊ k) ⟫ ⟫ ≈ S₀₁.⟪ N₂.⟪ Λ□ (₄₊ k) ⟫ ⟫ • CCZX
Eq293 k = (₁₊ (₄₊ k)) ⊢ K • Λ□ (₄₊ k) ≈ Λ□ (₄₊ k) • K
Eq294 k = (₁₊ (₄₊ k)) ⊢ Λ□ (₄₊ k) ≈
  CCZX • S₀₁.⟪ CCZX₁₃ ⟫ • C k • S₀₁.⟪ CCXZ₁₃ ⟫ • CCXZ • S₀₁.⟪ CCZX₁₃ ⟫ • C k • S₀₁.⟪ CCXZ₁₃ ⟫
Eq295 k = (₁₊ (₄₊ k)) ⊢ Λ□ (₄₊ k) ≈ ZX₃ • (Kᵇ • C k • Kᵇ′) • XZ₃ • (Kᵇ • C k • Kᵇ′)
Eq305 k = (₁₊ (₄₊ k)) ⊢ (ΛXZ 1 ↓ᵏ (₃₊ k)) • B₁₀ (₂₊ k) • (ΛZX 1 ↓ᵏ (₃₊ k)) • B₁₀ (₂₊ k) ≈ Λ□ (₄₊ k)
Eq306 k = (₁₊ (₄₊ k)) ⊢ Ex ↑ ↑ • Λ□ (₄₊ k) ≈ Λ□ (₄₊ k) • Ex ↑ ↑
Eq336 k = (₁₊ (₄₊ k)) ⊢ Λ□ (₄₊ k) • B₁₀ (₂₊ k) ≈ B₁₀ (₂₊ k) • Λ□ (₄₊ k)

module _ (k : ℕ) (complete : Complete (₁₊ k)) where

  private
    open Tools ((₁₊ (₄₊ k)) VRel,_===_)
    open WordAlgebra ((₁₊ (₄₊ k)) VRel,_===_) using (comm-inv)

    Λ W V B A Ā C₃ D : Circuit (₁₊ (₄₊ k))
    Λ  = Λ□ (₄₊ k)
    W  = CCZX
    V  = CCXZ
    B  = B□ (₁₊ k)
    A  = S₀₁.⟪ CCZX₁₃ ⟫
    Ā  = S₀₁.⟪ CCXZ₁₃ ⟫
    C₃ = place 2 (Λ□ (₃₊ k))
    D  = Kᵇ • C k • Kᵇ′

    pass• : ∀ {c a w : Circuit (₁₊ (₄₊ k))} → (₁₊ (₄₊ k)) ⊢ c • a ≈ a • c →
            (₁₊ (₄₊ k)) ⊢ c • w ≈ w • c → (₁₊ (₄₊ k)) ⊢ c • (a • w) ≈ (a • w) • c
    pass• {c} {a} {w} ea ew = begin
      c • (a • w)     ≈⟨ sym assoc ⟩
      (c • a) • w     ≈⟨ front _ ea ⟩
      (a • c) • w     ≈⟨ assoc ⟩
      a • (c • w)     ≈⟨ back _ ew ⟩
      a • (w • c)     ≈⟨ sym assoc ⟩
      (a • w) • c ∎

    ------------------------------------------------------------------
    -- Conjugations of the wires 0–3 that commute

    S₀₁X₂ : (₁₊ (₄₊ k)) ⊢ S₀₁.⟪ X ↑ ↑ ⟫ ≈ X ↑ ↑
    S₀₁X₂ = S₀₁.⟪⟫-fix (low-comm Ex X)

    S₀₁N₂ : ∀ w → (₁₊ (₄₊ k)) ⊢ S₀₁.⟪ N₂.⟪ w ⟫ ⟫ ≈ N₂.⟪ S₀₁.⟪ w ⟫ ⟫
    S₀₁N₂ w = S₀₁.⟪⟫-•₃ S₀₁X₂ refl S₀₁X₂

    -- X on wire 2 under the swap of the wires 2 3 is X on wire 3.
    S₂₃X₂ : (₁₊ (₄₊ k)) ⊢ S₂₃.⟪ X ↑ ↑ ⟫ ≈ X ↑ ↑ ↑
    S₂₃X₂ = lemma-cong↑ (Ex ↑ • X ↑ • Ex ↑) (X ↑ ↑) (lemma-cong↑ (Ex • X • Ex) (X ↑) (L-sem (Ex • X • Ex) (X ↑) Eq.refl))

    S₂₃N₂ : ∀ w → (₁₊ (₄₊ k)) ⊢ S₂₃.⟪ N₂.⟪ w ⟫ ⟫ ≈ N₃.⟪ S₂₃.⟪ w ⟫ ⟫
    S₂₃N₂ w = S₂₃.⟪⟫-•₃ S₂₃X₂ refl S₂₃X₂

    S₂₃S₀₁ : ∀ w → (₁₊ (₄₊ k)) ⊢ S₂₃.⟪ S₀₁.⟪ w ⟫ ⟫ ≈ S₀₁.⟪ S₂₃.⟪ w ⟫ ⟫
    S₂₃S₀₁ w = S₂₃.⟪⟫-•₃ e refl e
      where
      e : (₁₊ (₄₊ k)) ⊢ S₂₃.⟪ Ex ↓ ⟫ ≈ Ex ↓
      e = S₂₃.⟪⟫-fix (sym (low-comm Ex Ex))

    S₂₃-ZX₃ : (₁₊ (₄₊ k)) ⊢ S₂₃.⟪ ZX₃ ⟫ ≈ ZX₃
    S₂₃-ZX₃ = S₂₃.⟪⟫-fix (sym eq214)

    S₂₃-XZ₃ : (₁₊ (₄₊ k)) ⊢ S₂₃.⟪ XZ₃ ⟫ ≈ XZ₃
    S₂₃-XZ₃ = S₂₃.⟪⟫-fix (sym eq214′)

    S₂₃-Kᵇ : (₁₊ (₄₊ k)) ⊢ S₂₃.⟪ Kᵇ ⟫ ≈ Kᵇ
    S₂₃-Kᵇ = trans (S₂₃S₀₁ ZX₃) (S₀₁.⟪⟫-cong S₂₃-ZX₃)

    S₂₃-Kᵇ′ : (₁₊ (₄₊ k)) ⊢ S₂₃.⟪ Kᵇ′ ⟫ ≈ Kᵇ′
    S₂₃-Kᵇ′ = trans (S₂₃S₀₁ XZ₃) (S₀₁.⟪⟫-cong S₂₃-XZ₃)

    ------------------------------------------------------------------
    -- (293)

    -- The box B of (269) under the swap of the wires 0 1 is C₃, the box
    -- on wire 0 with wire 2 idle.
    S₀₁-B : (₁₊ (₄₊ k)) ⊢ S₀₁.⟪ B ⟫ ≈ C₃
    S₀₁-B = begin
      Ex ↓ • ((Ex ↓ • Ex ↑ • Ex ↓) • Λ□ (₃₊ k) ↑ • (Ex ↓ • Ex ↑ • Ex ↓)) • Ex ↓
        ≈⟨ by-passoc (□ • ((□ • □ • □) • □ • (□ • □ • □)) • □) (((□ • □) • □ • □) • □ • (□ • □ • (□ • □))) Eq.refl ⟩
      ((Ex ↓ • Ex ↓) • Ex ↑ • Ex ↓) • Λ□ (₃₊ k) ↑ • (Ex ↓ • Ex ↑ • (Ex ↓ • Ex ↓))
        ≈⟨ cong (front _ Ex²) (back _ (back _ (back _ Ex²))) ⟩
      (ε • Ex ↑ • Ex ↓) • Λ□ (₃₊ k) ↑ • (Ex ↓ • Ex ↑ • ε)
        ≈⟨ by-passoc ((□ • □ • □) • □ • (□ • □ • □)) (((□ • □) • □) • □ • (□ • (□ • □))) Eq.refl ⟩
      ((ε • Ex ↑) • Ex ↓) • Λ□ (₃₊ k) ↑ • (Ex ↓ • (Ex ↑ • ε)) ∎

    S₀₁-C₃ : (₁₊ (₄₊ k)) ⊢ S₀₁.⟪ C₃ ⟫ ≈ B
    S₀₁-C₃ = S₀₁.⟪⟫-≈ˡ (sym S₀₁-B) (S₀₁.⟪⟫-⟪⟫ B)

    N₂-C₃ : (₁₊ (₄₊ k)) ⊢ N₂.⟪ C₃ ⟫ ≈ C₃
    N₂-C₃ = N₂.⟪⟫-fix (X-place 2 (Λ□ (₃₊ k)))

    ZX₃-C₃ : (₁₊ (₄₊ k)) ⊢ ZX₃ • C₃ ≈ C₃ • ZX₃
    ZX₃-C₃ = begin
      ZX₃ • C₃                  ≈⟨ back _ (sym (B₁₀↑-place k complete)) ⟩
      ZX₃ • B₁₀ (₁₊ k) ↑         ≈⟨ sym (eq291 k complete) ⟩
      B₁₀ (₁₊ k) ↑ • ZX₃         ≈⟨ front _ (B₁₀↑-place k complete) ⟩
      C₃ • ZX₃ ∎

    K-B : (₁₊ (₄₊ k)) ⊢ K • B ≈ B • K
    K-B = S₀₁.⟪⟫-≈ (N₂.⟪⟫-≈ ZX₃-C₃ (N₂.⟪⟫-•₂ refl N₂-C₃) (N₂.⟪⟫-•₂ N₂-C₃ refl))
                   (S₀₁.⟪⟫-•₂ refl S₀₁-C₃) (S₀₁.⟪⟫-•₂ S₀₁-C₃ refl)

  eq293 : Eq293 k
  eq293 = pass• eq216 (pass• K-B (pass• eq217 K-B))

  ----------------------------------------------------------------------
  -- (292)

  private
    S₀₁N₂B : (₁₊ (₄₊ k)) ⊢ S₀₁.⟪ N₂.⟪ B ⟫ ⟫ ≈ C₃
    S₀₁N₂B = trans (S₀₁N₂ B) (trans (N₂.⟪⟫-cong S₀₁-B) N₂-C₃)

    D-form : (₁₊ (₄₊ k)) ⊢ S₀₁.⟪ N₂.⟪ Λ ⟫ ⟫ ≈ °CZXC • C₃ • °CXZC • C₃
    D-form = trans (S₀₁.⟪⟫-cong (N₂.⟪⟫-•₄ refl refl refl refl))
                   (S₀₁.⟪⟫-•₄ refl S₀₁N₂B refl S₀₁N₂B)

    W-C₃ : (₁₊ (₄₊ k)) ⊢ CCZX • C₃ ≈ C₃ • CCZX
    W-C₃ = sym (eq287 (₁₊ k) complete)

  eq292 : Eq292 k
  eq292 = begin
    CCZX • S₀₁.⟪ N₂.⟪ Λ ⟫ ⟫              ≈⟨ back _ D-form ⟩
    CCZX • (°CZXC • C₃ • °CXZC • C₃)      ≈⟨ pass• eq139 (pass• W-C₃ (pass• eq140 W-C₃)) ⟩
    (°CZXC • C₃ • °CXZC • C₃) • CCZX      ≈⟨ front _ (sym D-form) ⟩
    S₀₁.⟪ N₂.⟪ Λ ⟫ ⟫ • CCZX ∎

  ----------------------------------------------------------------------
  -- (294)

  private
    -- The singly controlled ZX on wire 1 from the wires 0 3, placed with
    -- wire 2 idle: the network carrying the wires 0–2 up around it is the
    -- swaps of the wires 0 1 and 2 3.
    N-A : (₁₊ (₄₊ k)) ⊢ cyc⁻¹ 2 • Ex ↑ • cyc 3 ≈ Ex ↓ • Ex ↑ ↑
    N-A = perm-≈ {u = scyc⁻¹ 2 • S.σ S.↑ • scyc 3} {v = S.σ • (S.σ S.↑) S.↑}
            (λ { zero → Eq.refl ; (suc zero) → Eq.refl ; (suc (suc zero)) → Eq.refl
               ; (suc (suc (suc zero))) → Eq.refl ; (suc (suc (suc (suc _)))) → Eq.refl })

    M-A : (₁₊ (₄₊ k)) ⊢ cyc⁻¹ 3 • Ex ↑ • cyc 2 ≈ Ex ↑ ↑ • Ex ↓
    M-A = perm-≈ {u = scyc⁻¹ 3 • S.σ S.↑ • scyc 2} {v = (S.σ S.↑) S.↑ • S.σ}
            (λ { zero → Eq.refl ; (suc zero) → Eq.refl ; (suc (suc zero)) → Eq.refl
               ; (suc (suc (suc zero))) → Eq.refl ; (suc (suc (suc (suc _)))) → Eq.refl })

    sw-place : ∀ (u : Circuit 3) →
               (₁₊ (₄₊ k)) ⊢ Ex ↓ • (Ex ↑ ↑ • (top u ↓ᵏ (₁₊ k)) • Ex ↑ ↑) • Ex ↓ ≈
                             place 2 (Ex ↓ • (u ↓ᵏ (₁₊ k)) • Ex ↓)
    sw-place u = sym (begin
      cyc⁻¹ 2 • (Ex ↑ • (u ↓ᵏ (₁₊ k)) ↑ • Ex ↑) • cyc 2
        ≈⟨ back _ (front _ (back _ (front _ u↑))) ⟩
      cyc⁻¹ 2 • (Ex ↑ • (cyc 3 • u′ • cyc⁻¹ 3) • Ex ↑) • cyc 2
        ≈⟨ by-passoc (□ • (□ • (□ • □ • □) • □) • □) ((□ • □ • □) • □ • (□ • □ • □)) Eq.refl ⟩
      (cyc⁻¹ 2 • Ex ↑ • cyc 3) • u′ • (cyc⁻¹ 3 • Ex ↑ • cyc 2)
        ≈⟨ cong N-A (back _ M-A) ⟩
      (Ex ↓ • Ex ↑ ↑) • u′ • (Ex ↑ ↑ • Ex ↓)
        ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
      Ex ↓ • (Ex ↑ ↑ • u′ • Ex ↑ ↑) • Ex ↓ ∎)
      where
      u′ : Circuit (₁₊ (₄₊ k))
      u′ = top u ↓ᵏ (₁₊ k)

      u↑ : (₁₊ (₄₊ k)) ⊢ (u ↓ᵏ (₁₊ k)) ↑ ≈ cyc 3 • u′ • cyc⁻¹ 3
      u↑ = begin
        (u ↓ᵏ (₁₊ k)) ↑                           ≈⟨ sym right-unit ⟩
        (u ↓ᵏ (₁₊ k)) ↑ • ε                       ≈⟨ back _ (sym (cyc-cyc⁻¹ 3)) ⟩
        (u ↓ᵏ (₁₊ k)) ↑ • (cyc 3 • cyc⁻¹ 3)       ≈⟨ sym assoc ⟩
        ((u ↓ᵏ (₁₊ k)) ↑ • cyc 3) • cyc⁻¹ 3       ≈⟨ front _ (lnat 3 u) ⟩
        (cyc 3 • u′) • cyc⁻¹ 3                    ≈⟨ assoc ⟩
        cyc 3 • u′ • cyc⁻¹ 3 ∎

    A-place : (₁₊ (₄₊ k)) ⊢ A ≈ place 2 (Ex ↓ • CCZX • Ex ↓)
    A-place = sw-place CCZX

    Ā-place : (₁₊ (₄₊ k)) ⊢ Ā ≈ place 2 (Ex ↓ • CCXZ • Ex ↓)
    Ā-place = sw-place CCXZ

    -- B, one width down with wire 2 idle, in both forms of (269).
    B-place : (₁₊ (₄₊ k)) ⊢ B ≈ place 2 (B₁₀ (₁₊ k))
    B-place = sym (place-B□ (₁₊ k) complete)

    B-form₁ : (₁₊ (₄₊ k)) ⊢ B ≈ A • C k • Ā • C k
    B-form₁ = begin
      B
        ≈⟨ B-place ⟩
      place 2 (B₁₀ (₁₊ k))
        ≈⟨ sym (lemma-5-1 2 complete (sem-294a k)) ⟩
      place 2 ((Ex ↓ • CCZX • Ex ↓) • C₀ k • (Ex ↓ • CCXZ • Ex ↓) • C₀ k)
        ≈⟨ trans (place-• 2 (Ex ↓ • CCZX • Ex ↓) (C₀ k • (Ex ↓ • CCXZ • Ex ↓) • C₀ k))
                 (back _ (trans (place-• 2 (C₀ k) ((Ex ↓ • CCXZ • Ex ↓) • C₀ k))
                                (back _ (place-• 2 (Ex ↓ • CCXZ • Ex ↓) (C₀ k))))) ⟩
      place 2 (Ex ↓ • CCZX • Ex ↓) • C k • place 2 (Ex ↓ • CCXZ • Ex ↓) • C k
        ≈⟨ cong (sym A-place) (back _ (front _ (sym Ā-place))) ⟩
      A • C k • Ā • C k ∎

    B-form₂ : (₁₊ (₄₊ k)) ⊢ B ≈ C k • A • C k • Ā
    B-form₂ = begin
      B
        ≈⟨ B-place ⟩
      place 2 (B₁₀ (₁₊ k))
        ≈⟨ sym (lemma-5-1 2 complete (sem-294b k)) ⟩
      place 2 (C₀ k • (Ex ↓ • CCZX • Ex ↓) • C₀ k • (Ex ↓ • CCXZ • Ex ↓))
        ≈⟨ trans (place-• 2 (C₀ k) ((Ex ↓ • CCZX • Ex ↓) • C₀ k • (Ex ↓ • CCXZ • Ex ↓)))
                 (back _ (trans (place-• 2 (Ex ↓ • CCZX • Ex ↓) (C₀ k • (Ex ↓ • CCXZ • Ex ↓)))
                                (back _ (place-• 2 (C₀ k) (Ex ↓ • CCXZ • Ex ↓))))) ⟩
      C k • place 2 (Ex ↓ • CCZX • Ex ↓) • C k • place 2 (Ex ↓ • CCXZ • Ex ↓)
        ≈⟨ back _ (cong (sym A-place) (back _ (sym Ā-place))) ⟩
      C k • A • C k • Ā ∎

    -- C around CCXZ, one width down with wire 3 idle.
    CVC : (₁₊ (₄₊ k)) ⊢ C k • V • C k ≈ V
    CVC = begin
      C k • V • C k
        ≈⟨ cong (place-swap (Λ□ (₂₊ k))) (cong (sym (place-low 3 CCXZ)) (place-swap (Λ□ (₂₊ k)))) ⟩
      place 3 (C₀ k) • place 3 (CCXZ {0} ↓ᵏ (₁₊ k)) • place 3 (C₀ k)
        ≈⟨ sym (trans (place-• 3 (C₀ k) ((CCXZ {0} ↓ᵏ (₁₊ k)) • C₀ k))
                      (back _ (place-• 3 (CCXZ {0} ↓ᵏ (₁₊ k)) (C₀ k)))) ⟩
      place 3 (C₀ k • (CCXZ {0} ↓ᵏ (₁₊ k)) • C₀ k)
        ≈⟨ lemma-5-1 3 complete (sem-294c k) ⟩
      place 3 (CCXZ {0} ↓ᵏ (₁₊ k))
        ≈⟨ place-low 3 CCXZ ⟩
      V ∎

  eq294 : Eq294 k
  eq294 = begin
    W • B • V • B
      ≈⟨ back _ (cong B-form₁ (back _ B-form₂)) ⟩
    W • (A • C k • Ā • C k) • V • (C k • A • C k • Ā)
      ≈⟨ by-passoc (□ • (□ • □ • □ • □) • □ • (□ • □ • □ • □)) (□ • □ • □ • □ • (□ • □ • □) • □ • □ • □) Eq.refl ⟩
    W • A • C k • Ā • (C k • V • C k) • A • C k • Ā
      ≈⟨ back _ (back _ (back _ (back _ (front _ CVC)))) ⟩
    W • A • C k • Ā • V • A • C k • Ā ∎

  ----------------------------------------------------------------------
  -- (295)

  private
    K′-V : (₁₊ (₄₊ k)) ⊢ K′ • V ≈ V • K′
    K′-V = sym (comm-inv K-K′ eq209 (sym eq217))

    -- The middle of (294), the merges carried through CCXZ.
    mid-V : (₁₊ (₄₊ k)) ⊢ Ā • V • A ≈ Kᵇ′ • V • Kᵇ
    mid-V = begin
      Ā • V • A                     ≈⟨ cong (sym eq222) (back _ (sym eq221)) ⟩
      (Kᵇ′ • K′) • V • (K • Kᵇ)     ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □) • □ • □) Eq.refl ⟩
      Kᵇ′ • (K′ • V) • K • Kᵇ       ≈⟨ back _ (front _ K′-V) ⟩
      Kᵇ′ • (V • K′) • K • Kᵇ       ≈⟨ by-passoc (□ • (□ • □) • □ • □) (□ • □ • (□ • □) • □) Eq.refl ⟩
      Kᵇ′ • V • (K′ • K) • Kᵇ       ≈⟨ back _ (back _ (trans (front _ eq209) left-unit)) ⟩
      Kᵇ′ • V • Kᵇ ∎

    -- ZX₃ white on wire 3 passes Kᵇ: (240) for ZX₃ and K, under X on
    -- wire 2 and the swap of the wires 2 3.
    N₂-K : (₁₊ (₄₊ k)) ⊢ N₂.⟪ K ⟫ ≈ Kᵇ
    N₂-K = trans (N₂.⟪⟫-cong (S₀₁N₂ ZX₃)) (N₂.⟪⟫-⟪⟫ Kᵇ)

    N₂ZX₃-Kᵇ : (₁₊ (₄₊ k)) ⊢ N₂.⟪ ZX₃ ⟫ • Kᵇ ≈ Kᵇ • N₂.⟪ ZX₃ ⟫
    N₂ZX₃-Kᵇ = N₂.⟪⟫-≈ (eq240 true true true true true true)
                        (N₂.⟪⟫-•₂ refl N₂-K) (N₂.⟪⟫-•₂ N₂-K refl)

    S₂₃N₂ZX₃ : (₁₊ (₄₊ k)) ⊢ S₂₃.⟪ N₂.⟪ ZX₃ ⟫ ⟫ ≈ N₃.⟪ ZX₃ ⟫
    S₂₃N₂ZX₃ = trans (S₂₃N₂ ZX₃) (N₃.⟪⟫-cong S₂₃-ZX₃)

    °ZX₃-Kᵇ : (₁₊ (₄₊ k)) ⊢ N₃.⟪ ZX₃ ⟫ • Kᵇ ≈ Kᵇ • N₃.⟪ ZX₃ ⟫
    °ZX₃-Kᵇ = S₂₃.⟪⟫-≈ N₂ZX₃-Kᵇ (S₂₃.⟪⟫-•₂ S₂₃N₂ZX₃ S₂₃-Kᵇ) (S₂₃.⟪⟫-•₂ S₂₃-Kᵇ S₂₃N₂ZX₃)

    KᵇKᵇ′ : (₁₊ (₄₊ k)) ⊢ Kᵇ • Kᵇ′ ≈ ε
    KᵇKᵇ′ = trans (sym (S₀₁.⟪⟫-• ZX₃ XZ₃)) (trans (S₀₁.⟪⟫-cong eq208′) S₀₁.⟪⟫-ε)

    Kᵇ′Kᵇ : (₁₊ (₄₊ k)) ⊢ Kᵇ′ • Kᵇ ≈ ε
    Kᵇ′Kᵇ = trans (sym (S₀₁.⟪⟫-• XZ₃ ZX₃)) (trans (S₀₁.⟪⟫-cong eq208) S₀₁.⟪⟫-ε)

    °ZX₃-Kᵇ′ : (₁₊ (₄₊ k)) ⊢ N₃.⟪ ZX₃ ⟫ • Kᵇ′ ≈ Kᵇ′ • N₃.⟪ ZX₃ ⟫
    °ZX₃-Kᵇ′ = comm-inv KᵇKᵇ′ Kᵇ′Kᵇ °ZX₃-Kᵇ

    -- C is B□ k one wire up (one width down, wire 3 idle), which passes
    -- ZX₃, (290); and X on wire 3 does not see it.
    C-B□↑ : (₁₊ (₄₊ k)) ⊢ C k ≈ B□ k ↑
    C-B□↑ = trans (place-swap (Λ□ (₂₊ k))) (trans (lemma-5-1 3 complete (sem-C₀-yB k)) (place-yB k))

    ZX₃-C : (₁₊ (₄₊ k)) ⊢ ZX₃ • C k ≈ C k • ZX₃
    ZX₃-C = begin
      ZX₃ • C k         ≈⟨ back _ C-B□↑ ⟩
      ZX₃ • B□ k ↑      ≈⟨ sym (eq290 k complete) ⟩
      B□ k ↑ • ZX₃      ≈⟨ front _ (sym C-B□↑) ⟩
      C k • ZX₃ ∎

    N₃-C : (₁₊ (₄₊ k)) ⊢ N₃.⟪ C k ⟫ ≈ C k
    N₃-C = N₃.⟪⟫-fix (begin
      X ↑ ↑ ↑ • C k                  ≈⟨ back _ (place-swap (Λ□ (₂₊ k))) ⟩
      X ↑ ↑ ↑ • place 3 (C₀ k)       ≈⟨ X-place 3 (C₀ k) ⟩
      place 3 (C₀ k) • X ↑ ↑ ↑       ≈⟨ front _ (sym (place-swap (Λ□ (₂₊ k)))) ⟩
      C k • X ↑ ↑ ↑ ∎)

    °ZX₃-C : (₁₊ (₄₊ k)) ⊢ N₃.⟪ ZX₃ ⟫ • C k ≈ C k • N₃.⟪ ZX₃ ⟫
    °ZX₃-C = N₃.⟪⟫-≈ ZX₃-C (N₃.⟪⟫-•₂ refl N₃-C) (N₃.⟪⟫-•₂ N₃-C refl)

    °ZX₃-D : (₁₊ (₄₊ k)) ⊢ N₃.⟪ ZX₃ ⟫ • D ≈ D • N₃.⟪ ZX₃ ⟫
    °ZX₃-D = pass• °ZX₃-Kᵇ (pass• °ZX₃-C °ZX₃-Kᵇ′)

    °ZX₃°XZ₃ : (₁₊ (₄₊ k)) ⊢ N₃.⟪ ZX₃ ⟫ • N₃.⟪ XZ₃ ⟫ ≈ ε
    °ZX₃°XZ₃ = trans (sym (N₃.⟪⟫-• ZX₃ XZ₃)) (trans (N₃.⟪⟫-cong eq208′) N₃.⟪⟫-ε)

    WDVD : (₁₊ (₄₊ k)) ⊢ W • D • V • D ≈ ZX₃ • D • XZ₃ • D
    WDVD = begin
      W • D • V • D
        ≈⟨ cong (sym eq223′) (back _ (front _ (sym eq224))) ⟩
      (ZX₃ • N₃.⟪ ZX₃ ⟫) • D • (N₃.⟪ XZ₃ ⟫ • XZ₃) • D
        ≈⟨ by-passoc ((□ • □) • □ • (□ • □) • □) (□ • (□ • □) • □ • □ • □) Eq.refl ⟩
      ZX₃ • (N₃.⟪ ZX₃ ⟫ • D) • N₃.⟪ XZ₃ ⟫ • XZ₃ • D
        ≈⟨ back _ (front _ °ZX₃-D) ⟩
      ZX₃ • (D • N₃.⟪ ZX₃ ⟫) • N₃.⟪ XZ₃ ⟫ • XZ₃ • D
        ≈⟨ by-passoc (□ • (□ • □) • □ • □ • □) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
      ZX₃ • D • (N₃.⟪ ZX₃ ⟫ • N₃.⟪ XZ₃ ⟫) • XZ₃ • D
        ≈⟨ back _ (back _ (trans (front _ °ZX₃°XZ₃) left-unit)) ⟩
      ZX₃ • D • XZ₃ • D ∎

  eq295 : Eq295 k
  eq295 = begin
    Λ
      ≈⟨ sym (trans (front _ eq209) left-unit) ⟩
    (K′ • K) • Λ
      ≈⟨ trans assoc (back _ eq293) ⟩
    K′ • (Λ • K)
      ≈⟨ back _ (front _ eq294) ⟩
    K′ • ((W • A • C k • Ā • V • A • C k • Ā) • K)
      ≈⟨ by-passoc (□ • ((□ • □ • □ • □ • □ • □ • □ • □) • □)) ((□ • □) • □ • □ • □ • □ • □ • □ • (□ • □)) Eq.refl ⟩
    (K′ • W) • A • C k • Ā • V • A • C k • (Ā • K)
      ≈⟨ cong eq218 (back _ (back _ (back _ (back _ (back _ (back _ eq226)))))) ⟩
    (W • K′) • A • C k • Ā • V • A • C k • Kᵇ′
      ≈⟨ by-passoc ((□ • □) • □ • □ • □ • □ • □ • □ • □) (□ • (□ • □) • □ • □ • □ • □ • □ • □) Eq.refl ⟩
    W • (K′ • A) • C k • Ā • V • A • C k • Kᵇ′
      ≈⟨ back _ (front _ eq225) ⟩
    W • Kᵇ • C k • Ā • V • A • C k • Kᵇ′
      ≈⟨ by-passoc (□ • □ • □ • □ • □ • □ • □ • □) (□ • □ • □ • (□ • □ • □) • □ • □) Eq.refl ⟩
    W • Kᵇ • C k • (Ā • V • A) • C k • Kᵇ′
      ≈⟨ back _ (back _ (back _ (front _ mid-V))) ⟩
    W • Kᵇ • C k • (Kᵇ′ • V • Kᵇ) • C k • Kᵇ′
      ≈⟨ by-passoc (□ • □ • □ • (□ • □ • □) • □ • □) (□ • (□ • □ • □) • □ • (□ • □ • □)) Eq.refl ⟩
    W • D • V • D
      ≈⟨ WDVD ⟩
    ZX₃ • D • XZ₃ • D ∎

  ----------------------------------------------------------------------
  -- (306)

  private
    S₂₃-C : (₁₊ (₄₊ k)) ⊢ S₂₃.⟪ C k ⟫ ≈ C k
    S₂₃-C = S₂₃.⟪⟫-fix (swap-idle₂₃ (Λ□ (₂₊ k)))

    S₂₃-D : (₁₊ (₄₊ k)) ⊢ S₂₃.⟪ D ⟫ ≈ D
    S₂₃-D = S₂₃.⟪⟫-•₃ S₂₃-Kᵇ S₂₃-C S₂₃-Kᵇ′

  eq306 : Eq306 k
  eq306 = S₂₃.⟪⟫-comm (begin
    S₂₃.⟪ Λ ⟫                          ≈⟨ S₂₃.⟪⟫-cong eq295 ⟩
    S₂₃.⟪ ZX₃ • D • XZ₃ • D ⟫          ≈⟨ S₂₃.⟪⟫-•₄ S₂₃-ZX₃ S₂₃-D S₂₃-XZ₃ S₂₃-D ⟩
    ZX₃ • D • XZ₃ • D                  ≈⟨ sym eq295 ⟩
    Λ ∎)

  ----------------------------------------------------------------------
  -- (305)

  private
    B₁₀′ Dw : Circuit (₁₊ (₄₊ k))
    B₁₀′ = S₀₁.⟪ Λ ⟫
    Dw   = S₀₁.⟪ N₂.⟪ Λ ⟫ ⟫

    -- (301), (302) under the swap of the wires 0 1.
    merge₁ : (₁₊ (₄₊ k)) ⊢ B₁₀′ • Dw ≈ B
    merge₁ = S₀₁.⟪⟫-≈ (eq301 (₁₊ k) complete) (S₀₁.⟪⟫-• Λ (N₂.⟪ Λ ⟫)) S₀₁-C₃

    merge₂ : (₁₊ (₄₊ k)) ⊢ Dw • B₁₀′ ≈ B
    merge₂ = S₀₁.⟪⟫-≈ (eq302 (₁₊ k) complete) (S₀₁.⟪⟫-• (N₂.⟪ Λ ⟫) Λ) S₀₁-C₃

    DD : (₁₊ (₄₊ k)) ⊢ Dw • Dw ≈ ε
    DD = S₀₁.⟪⟫-invol (N₂.⟪⟫-invol (eq299 (₁₊ k) complete))

    D-W : (₁₊ (₄₊ k)) ⊢ Dw • W ≈ W • Dw
    D-W = sym eq292

    -- CCZX and CCXZ white on wire 2 pass B₁₀: (292) under X on wire 2.
    N₂D : (₁₊ (₄₊ k)) ⊢ N₂.⟪ Dw ⟫ ≈ B₁₀′
    N₂D = trans (sym (S₀₁N₂ (N₂.⟪ Λ ⟫))) (S₀₁.⟪⟫-cong (N₂.⟪⟫-⟪⟫ Λ))

    °W-B₁₀ : (₁₊ (₄₊ k)) ⊢ N₂.⟪ W ⟫ • B₁₀′ ≈ B₁₀′ • N₂.⟪ W ⟫
    °W-B₁₀ = N₂.⟪⟫-≈ eq292 (N₂.⟪⟫-•₂ refl N₂D) (N₂.⟪⟫-•₂ N₂D refl)

    °W°V : (₁₊ (₄₊ k)) ⊢ N₂.⟪ W ⟫ • N₂.⟪ V ⟫ ≈ ε
    °W°V = trans (sym (N₂.⟪⟫-• W V)) (trans (N₂.⟪⟫-cong eq117) N₂.⟪⟫-ε)

    B₁₀-°V : (₁₊ (₄₊ k)) ⊢ B₁₀′ • N₂.⟪ V ⟫ ≈ N₂.⟪ V ⟫ • B₁₀′
    B₁₀-°V = comm-inv °W°V °V°W (sym °W-B₁₀)
      where
      °V°W : (₁₊ (₄₊ k)) ⊢ N₂.⟪ V ⟫ • N₂.⟪ W ⟫ ≈ ε
      °V°W = trans (sym (N₂.⟪⟫-• V W)) (trans (N₂.⟪⟫-cong eq118) N₂.⟪⟫-ε)

    mid305 : (₁₊ (₄₊ k)) ⊢ N₂.⟪ V ⟫ • B₁₀′ • N₂.⟪ W ⟫ ≈ B₁₀′
    mid305 = begin
      N₂.⟪ V ⟫ • B₁₀′ • N₂.⟪ W ⟫       ≈⟨ sym assoc ⟩
      (N₂.⟪ V ⟫ • B₁₀′) • N₂.⟪ W ⟫     ≈⟨ front _ (sym B₁₀-°V) ⟩
      (B₁₀′ • N₂.⟪ V ⟫) • N₂.⟪ W ⟫     ≈⟨ assoc ⟩
      B₁₀′ • N₂.⟪ V ⟫ • N₂.⟪ W ⟫       ≈⟨ back _ (trans (sym (N₂.⟪⟫-• V W)) (trans (N₂.⟪⟫-cong eq118) N₂.⟪⟫-ε)) ⟩
      B₁₀′ • ε                         ≈⟨ right-unit ⟩
      B₁₀′ ∎

  eq305 : Eq305 k
  eq305 = begin
    (ΛXZ 1 ↓ᵏ (₃₊ k)) • B₁₀′ • (ΛZX 1 ↓ᵏ (₃₊ k)) • B₁₀′
      ≈⟨ cong (sym eq138) (back _ (front _ (sym eq136))) ⟩
    (V • N₂.⟪ V ⟫) • B₁₀′ • (N₂.⟪ W ⟫ • W) • B₁₀′
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □) • □) (□ • (□ • □ • □) • □ • □) Eq.refl ⟩
    V • (N₂.⟪ V ⟫ • B₁₀′ • N₂.⟪ W ⟫) • W • B₁₀′
      ≈⟨ back _ (front _ mid305) ⟩
    V • B₁₀′ • W • B₁₀′
      ≈⟨ back _ (back _ (sym (trans (front _ DD) left-unit))) ⟩
    V • B₁₀′ • (Dw • Dw) • W • B₁₀′
      ≈⟨ by-passoc (□ • □ • (□ • □) • □ • □) (□ • (□ • □) • (□ • □) • □) Eq.refl ⟩
    V • (B₁₀′ • Dw) • (Dw • W) • B₁₀′
      ≈⟨ back _ (back _ (front _ D-W)) ⟩
    V • (B₁₀′ • Dw) • (W • Dw) • B₁₀′
      ≈⟨ by-passoc (□ • (□ • □) • (□ • □) • □) (□ • (□ • □) • □ • (□ • □)) Eq.refl ⟩
    V • (B₁₀′ • Dw) • W • (Dw • B₁₀′)
      ≈⟨ back _ (cong merge₁ (back _ merge₂)) ⟩
    V • B • W • B
      ≈⟨ sym (eq286 (₁₊ k)) ⟩
    Λ ∎

  ----------------------------------------------------------------------
  -- (336), all controls black

  private
    B₁₀² : (₁₊ (₄₊ k)) ⊢ B₁₀′ • B₁₀′ ≈ ε
    B₁₀² = S₀₁.⟪⟫-invol (eq299 (₁₊ k) complete)

    -- The merges read the other way.
    BB₁₀ : (₁₊ (₄₊ k)) ⊢ B • B₁₀′ ≈ Dw
    BB₁₀ = begin
      B • B₁₀′               ≈⟨ front _ (sym merge₂) ⟩
      (Dw • B₁₀′) • B₁₀′     ≈⟨ assoc ⟩
      Dw • (B₁₀′ • B₁₀′)     ≈⟨ back _ B₁₀² ⟩
      Dw • ε                 ≈⟨ right-unit ⟩
      Dw ∎

    B₁₀B : (₁₊ (₄₊ k)) ⊢ B₁₀′ • B ≈ Dw
    B₁₀B = begin
      B₁₀′ • B               ≈⟨ back _ (sym merge₁) ⟩
      B₁₀′ • (B₁₀′ • Dw)     ≈⟨ sym assoc ⟩
      (B₁₀′ • B₁₀′) • Dw     ≈⟨ front _ B₁₀² ⟩
      ε • Dw                 ≈⟨ left-unit ⟩
      Dw ∎

    DB : (₁₊ (₄₊ k)) ⊢ Dw • B ≈ B₁₀′
    DB = begin
      Dw • B                 ≈⟨ back _ (sym merge₂) ⟩
      Dw • (Dw • B₁₀′)       ≈⟨ sym assoc ⟩
      (Dw • Dw) • B₁₀′       ≈⟨ front _ DD ⟩
      ε • B₁₀′               ≈⟨ left-unit ⟩
      B₁₀′ ∎

    BD : (₁₊ (₄₊ k)) ⊢ B • Dw ≈ B₁₀′
    BD = begin
      B • Dw                 ≈⟨ front _ (sym merge₁) ⟩
      (B₁₀′ • Dw) • Dw       ≈⟨ assoc ⟩
      B₁₀′ • (Dw • Dw)       ≈⟨ back _ DD ⟩
      B₁₀′ • ε               ≈⟨ right-unit ⟩
      B₁₀′ ∎

    D-B : (₁₊ (₄₊ k)) ⊢ Dw • B ≈ B • Dw
    D-B = trans DB (sym BD)

    D-V : (₁₊ (₄₊ k)) ⊢ Dw • V ≈ V • Dw
    D-V = comm-inv eq117 eq118 D-W

  eq336 : Eq336 k
  eq336 = begin
    (W • B • V • B) • B₁₀′           ≈⟨ by-passoc ((□ • □ • □ • □) • □) (□ • □ • □ • (□ • □)) Eq.refl ⟩
    W • B • V • (B • B₁₀′)           ≈⟨ back _ (back _ (back _ BB₁₀)) ⟩
    W • B • V • Dw                   ≈⟨ by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl ⟩
    (W • B • V) • Dw                 ≈⟨ sym (pass• D-W (pass• D-B D-V)) ⟩
    Dw • W • B • V                   ≈⟨ front _ (sym B₁₀B) ⟩
    (B₁₀′ • B) • W • B • V           ≈⟨ assoc ⟩
    B₁₀′ • (B • W • B • V)           ≈⟨ back _ (sym (eq300 (₁₊ k) complete)) ⟩
    B₁₀′ • Λ ∎
