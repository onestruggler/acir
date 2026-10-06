------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoded double exchange on four qubits, and the cores of rules
-- (43) and (44) (Clément, Appendix E.5 at n = 4, (361), from Lemma D.5)
--
-- On four wires, between the negations, the decoded X_[0,3] X_[1,2] is
-- Cc = (Yb • B₁ • Λ) • (XW • (XB • Yb • ZXB) • XWi) with XB, ZXB the
-- triply controlled rotations XZ₃, ZX₃, XW, XWi the same white on wire
-- 1, Yb the rotation on wire 1, B₁ the box on wire 1 and Λ the box.
-- (361) says Cc ≈ Λ • Y and Cc ≈ Yi • Λ with Y, Yi the doubly controlled
-- rotations one wire up.  Canon361's argument, its inputs from Lemma D.5:
-- the merges on wire 1 are PForms' and their inverses, (355) is W4.Box,
-- and Lemma 8.5, W • Yb • Wi ≈ X • Yb • X, is under the lower swap
-- Y • XB • Yi ≈ XW.  That is a D-trick over the colour of wire 2: Y is
-- the rotation on wire 1 controlled by wire 3 times Yi white on wire 2
-- (one three-wire evaluation); the white factor passes XB — in the form
-- c G c G of (213), with G = ΛH₂′ in its rotation form, every letter of
-- either meets the other on its own triple of wires or on disjoint ones
-- — and the other factor conjugates XB to XW, which is the same for the
-- rotation controlled by wire 2 under the swap of the wires 2 3, and
-- that, letter by letter in the same forms, turns the control of G on
-- wire 1 white.  Then rule (44) is HG passing Λ ((338), W4.Cores) and Y
-- (letter by letter), and rule (43) is Canon43's L1 with the D-trick a
-- single merge, (171ᶜ), in the frame of the swap of the wires 2 3, and
-- Canon43's hgform with (278) from ZXPass and (172) for its Zp.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.Lemma88.W4.Eq361
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (true ; false)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; X² ; CZ² ; CH² ; Ex²)
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (evaluated)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (eq117 ; eq118 ; PP-CZ₂₀ ; module N₁ ; module N₂ ; module PP↓)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
  using (module S₀₁ ; module S₁₂ ; module S₂₃ ; L₀ ; U₀ ; O₀ ; U ; P₀₃ ; P₁₃ ; P₂₃ ;
         L-sem ; U-sem ; U₃-sem ; O-L ; U-S₂₃ ; O-S₂₃ ; P₀₃-U ; comm-13-03)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃ using (box₃ ; CZ₃₀ ; CZ₃₀-P)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Box complete₂ complete₃
  using (eq156 ; eq157 ; eq159 ; eq161 ; eq163 ; eq166)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃
  using (box₃′ ; CCZX₂₃ ; CCXZ₂₃ ; eq172 ; eq174)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃
  using (ZX₃ ; XZ₃ ; eq208 ; eq208′ ; eq213 ; eq214′ ; box₃′² ; ΛH₂′²)
open import Examples.Groups.Real-Clifford+CH.FourQubit.ControlledH complete₂ complete₃
  using (ΛH₂′ ; °ΛH₂′ ; ΛH₂′-rot)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates complete₂ complete₃ using (eq171ᶜ ; ΛH₀₁-PP)
open import Examples.Groups.Real-Clifford+CH.FourQubit.PForms complete₂ complete₃ using (merge₁ ; merge₁′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Permutations complete₂ complete₃
  using (S₂₃-X₁ ; S₂₃-ΛH₀₁)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Crossed complete₂ complete₃ using (X₂-S₁₂ΛH₀₁)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZXPass complete₂ complete₃ using (eq278)
open import Examples.Groups.Real-Clifford+CH.Lemma88.XX0312 {1} using (Cc)
open import Examples.Groups.Real-Clifford+CH.Lemma88.W3.Kit complete₂ using (s12₃)
open import Examples.Groups.Real-Clifford+CH.Lemma88.W4.Box complete₂ complete₃ using (core′₁)
open import Examples.Groups.Real-Clifford+CH.Lemma88.W4.Cores complete₂ complete₃ using (HG-box₃ ; HG-P₁₃CZ)

open Tools (4 VRel,_===_)
open WordAlgebra (4 VRel,_===_) using (comm-abab ; inv-unique ; unwrap′)

private
  -- The gates.
  Λ B₁ XB ZXB XW XWi Yb Ybi Y Yi W Wi HG G °G R : Circuit 4
  Λ   = Λ□ 3
  B₁  = box₃′
  XB  = XZ₃
  ZXB = ZX₃
  XW  = X ↑ • XB • X ↑
  XWi = X ↑ • ZXB • X ↑
  Yb  = Ex • XB • Ex
  Ybi = Ex • ZXB • Ex
  Y   = CCXZ ↑
  Yi  = CCZX ↑
  W   = CCXZ₂₃
  Wi  = CCZX₂₃
  HG  = Ex ↓ • ΛH 2 • Ex ↓
  G   = ΛH₂′
  °G  = °ΛH₂′
  R   = S₁₂.⟪ HG ⟫

  module TX = Conj {4} X X²

  pass₂ : ∀ {a u v : Circuit 4} → a • u ≈ u • a → a • v ≈ v • a → a • (u • v) ≈ (u • v) • a
  pass₂ eu ev = trans (sym assoc) (trans (front _ eu) (trans assoc (trans (back _ ev) (sym assoc))))

  -- Conjugation by a pair of inverses distributes.
  cj-• : ∀ {p q a b : Circuit 4} → q • p ≈ ε → p • (a • b) • q ≈ (p • a • q) • (p • b • q)
  cj-• {p} {q} {a} {b} qp = sym (begin
    (p • a • q) • (p • b • q)     ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
    p • a • (q • p) • b • q       ≈⟨ back _ (back _ (trans (front _ qp) left-unit)) ⟩
    p • a • b • q                 ≈⟨ back _ (sym assoc) ⟩
    p • (a • b) • q ∎)

  cj-4 : ∀ {p q a b d f : Circuit 4} → q • p ≈ ε →
         p • (a • b • d • f) • q ≈ (p • a • q) • (p • b • q) • (p • d • q) • (p • f • q)
  cj-4 qp = trans (cj-• qp) (back _ (trans (cj-• qp) (back _ (cj-• qp))))

  cj-fix : ∀ {p q a : Circuit 4} → p • a ≈ a • p → p • q ≈ ε → p • a • q ≈ a
  cj-fix pa pq = trans (sym assoc) (trans (front _ pa) (trans assoc (trans (back _ pq) right-unit)))

  sX′ : S₀₁.⟪ X ↑ ⟫ ≈ X
  sX′ = L-sem (Ex • X ↑ • Ex) X Eq.refl

  -- Inverses.
  Y-Yi : Y • Yi ≈ ε
  Y-Yi = lemma-cong↑ (CCXZ • CCZX) ε eq118

  Yi-Y : Yi • Y ≈ ε
  Yi-Y = lemma-cong↑ (CCZX • CCXZ) ε eq117

  Λ² : Λ • Λ ≈ ε
  Λ² = eq166

  W-Wi : W • Wi ≈ ε
  W-Wi = trans (sym (S₀₁.⟪⟫-• Y Yi)) (trans (S₀₁.⟪⟫-cong Y-Yi) S₀₁.⟪⟫-ε)

  XWi-XW : XWi • XW ≈ ε
  XWi-XW = trans (sym (N₁.⟪⟫-• ZXB XB)) (trans (N₁.⟪⟫-cong eq208′) N₁.⟪⟫-ε)

  ----------------------------------------------------------------------
  -- The merges on wire 1 (PForms) and their inverses

  ZXB-XWi : ZXB • XWi ≈ Wi
  ZXB-XWi = merge₁′

  XW-XB : XW • XB ≈ W
  XW-XB = inv-unique (unwrap′ XWi-XW eq208′) W-Wi merge₁′

  XB-XW : XB • XW ≈ W
  XB-XW = inv-unique (unwrap′ eq208′ XWi-XW) W-Wi merge₁

  ----------------------------------------------------------------------
  -- Lemma 8.5 under the lower swap: Y • XB • Yi ≈ XW

  Y₂ Y₂i Y₃ Y₃i : Circuit 4
  Y₂  = U (ΛXZ 1)
  Y₂i = U (ΛZX 1)
  Y₃  = P₁₃ (ΛXZ 1)
  Y₃i = P₁₃ (ΛZX 1)

  -- Y is the rotation controlled by wire 3 times Yi white on wire 2.
  ysplit : Y ≈ Y₃ • N₂.⟪ Yi ⟫
  ysplit = U₃-sem CCXZ (O₀ (ΛXZ 1) • (X ↑ • CCZX • X ↑)) Eq.refl

  yisplit : Yi ≈ N₂.⟪ Y ⟫ • Y₃i
  yisplit = U₃-sem CCZX ((X ↑ • CCXZ • X ↑) • O₀ (ΛZX 1)) Eq.refl

  V-Vi : N₂.⟪ Yi ⟫ • N₂.⟪ Y ⟫ ≈ ε
  V-Vi = trans (sym (N₂.⟪⟫-• Yi Y)) (trans (N₂.⟪⟫-cong Yi-Y) N₂.⟪⟫-ε)

  -- The rotation and the H gate of (213), as letters.
  c : Circuit 4
  c = CZ₃₀

  Rg Rg⁻ e′ : Circuit 4
  Rg  = P₂₃ CZ • P₁₃ HC • P₂₃ CZ • P₁₃ HC
  Rg⁻ = P₁₃ HC • P₂₃ CZ • P₁₃ HC • P₂₃ CZ
  e′  = P₀₃ CH

  Rg₃ Rg⁻₃ : Circuit 3
  Rg₃  = U₀ CZ • O₀ HC • U₀ CZ • O₀ HC
  Rg⁻₃ = O₀ HC • U₀ CZ • O₀ HC • U₀ CZ

  -- The white factor passes XB.
  Vform : N₂.⟪ Yi ⟫ ≈ U °CH • P₁₃ CZ • U °CH • P₁₃ CZ
  Vform = U₃-sem (X ↑ • CCZX • X ↑) (L₀ °CH • O₀ CZ • L₀ °CH • O₀ CZ) Eq.refl

  c-V : c • N₂.⟪ Yi ⟫ ≈ N₂.⟪ Yi ⟫ • c
  c-V = trans (front _ CZ₃₀-P) (trans (back _ Vform)
          (trans (comm-abab (P₀₃-U CZ °CH) (sym (comm-13-03 CZ CZ (evaluated Eq.refl))))
                 (trans (front _ (sym Vform)) (back _ (sym CZ₃₀-P)))))

  e′-V : e′ • N₂.⟪ Yi ⟫ ≈ N₂.⟪ Yi ⟫ • e′
  e′-V = trans (back _ Vform)
           (trans (comm-abab (P₀₃-U CH °CH) (sym (comm-13-03 CZ CH (evaluated Eq.refl))))
                  (front _ (sym Vform)))

  V-Rg : N₂.⟪ Yi ⟫ • Rg ≈ Rg • N₂.⟪ Yi ⟫
  V-Rg = U₃-sem ((X ↑ • CCZX • X ↑) • Rg₃) (Rg₃ • (X ↑ • CCZX • X ↑)) Eq.refl

  V-Rg⁻ : N₂.⟪ Yi ⟫ • Rg⁻ ≈ Rg⁻ • N₂.⟪ Yi ⟫
  V-Rg⁻ = U₃-sem ((X ↑ • CCZX • X ↑) • Rg⁻₃) (Rg⁻₃ • (X ↑ • CCZX • X ↑)) Eq.refl

  V-G : N₂.⟪ Yi ⟫ • G ≈ G • N₂.⟪ Yi ⟫
  V-G = trans (back _ ΛH₂′-rot)
          (trans (pass₂ V-Rg (pass₂ (sym e′-V) (pass₂ V-Rg⁻ (sym e′-V)))) (front _ (sym ΛH₂′-rot)))

  V-XB : N₂.⟪ Yi ⟫ • XB ≈ XB • N₂.⟪ Yi ⟫
  V-XB = trans (back _ eq213) (trans (comm-abab (sym c-V) V-G) (front _ (sym eq213)))

  -- The rotation controlled by wire 2 turns G's control on wire 1 white.
  Y₂i-Y₂ : Y₂i • Y₂ ≈ ε
  Y₂i-Y₂ = U-sem (ΛZX 1 • ΛXZ 1) ε Eq.refl

  Y₂-Y₂i : Y₂ • Y₂i ≈ ε
  Y₂-Y₂i = U-sem (ΛXZ 1 • ΛZX 1) ε Eq.refl

  y-c : Y₂ • c ≈ c • Y₂
  y-c = trans (back _ CZ₃₀-P) (trans (sym (P₀₃-U CZ (ΛXZ 1))) (front _ (sym CZ₃₀-P)))

  y-e : Y₂ • e′ ≈ e′ • Y₂
  y-e = sym (P₀₃-U CH (ΛXZ 1))

  n-c : N₁.⟪ c ⟫ ≈ c
  n-c = N₁.⟪⟫-fix (trans (back _ CZ₃₀-P) (trans (sym (P₀₃-U CZ X)) (front _ (sym CZ₃₀-P))))

  n-e : N₁.⟪ e′ ⟫ ≈ e′
  n-e = N₁.⟪⟫-fix (sym (P₀₃-U CH X))

  y-Rg : Y₂ • Rg • Y₂i ≈ N₁.⟪ Rg ⟫
  y-Rg = U₃-sem (L₀ (ΛXZ 1) • Rg₃ • L₀ (ΛZX 1)) (X • Rg₃ • X) Eq.refl

  y-Rg⁻ : Y₂ • Rg⁻ • Y₂i ≈ N₁.⟪ Rg⁻ ⟫
  y-Rg⁻ = U₃-sem (L₀ (ΛXZ 1) • Rg⁻₃ • L₀ (ΛZX 1)) (X • Rg⁻₃ • X) Eq.refl

  y-G : Y₂ • G • Y₂i ≈ N₁.⟪ G ⟫
  y-G = begin
    Y₂ • G • Y₂i
      ≈⟨ mid _ _ ΛH₂′-rot ⟩
    Y₂ • (Rg • e′ • Rg⁻ • e′) • Y₂i
      ≈⟨ cj-4 Y₂i-Y₂ ⟩
    (Y₂ • Rg • Y₂i) • (Y₂ • e′ • Y₂i) • (Y₂ • Rg⁻ • Y₂i) • (Y₂ • e′ • Y₂i)
      ≈⟨ cong y-Rg (cong ye (cong y-Rg⁻ ye)) ⟩
    N₁.⟪ Rg ⟫ • e′ • N₁.⟪ Rg⁻ ⟫ • e′
      ≈⟨ sym (N₁.⟪⟫-•₄ refl n-e refl n-e) ⟩
    N₁.⟪ Rg • e′ • Rg⁻ • e′ ⟫
      ≈⟨ N₁.⟪⟫-cong (sym ΛH₂′-rot) ⟩
    N₁.⟪ G ⟫ ∎
    where
    ye : Y₂ • e′ • Y₂i ≈ e′
    ye = cj-fix y-e Y₂-Y₂i

  A3 : Y₂ • XB • Y₂i ≈ XW
  A3 = begin
    Y₂ • XB • Y₂i
      ≈⟨ mid _ _ eq213 ⟩
    Y₂ • (c • G • c • G) • Y₂i
      ≈⟨ cj-4 Y₂i-Y₂ ⟩
    (Y₂ • c • Y₂i) • (Y₂ • G • Y₂i) • (Y₂ • c • Y₂i) • (Y₂ • G • Y₂i)
      ≈⟨ cong yc (cong y-G (cong yc y-G)) ⟩
    c • N₁.⟪ G ⟫ • c • N₁.⟪ G ⟫
      ≈⟨ sym (N₁.⟪⟫-•₄ n-c refl n-c refl) ⟩
    N₁.⟪ c • G • c • G ⟫
      ≈⟨ N₁.⟪⟫-cong (sym eq213) ⟩
    XW ∎
    where
    yc : Y₂ • c • Y₂i ≈ c
    yc = cj-fix y-c Y₂-Y₂i

  -- … and so does the rotation controlled by wire 3, under the swap of
  -- the wires 2 3.
  sXB : S₂₃.⟪ XB ⟫ ≈ XB
  sXB = S₂₃.⟪⟫-fix (sym eq214′)

  A3′ : Y₃ • XB • Y₃i ≈ XW
  A3′ = S₂₃.⟪⟫-≈ A3 (S₂₃.⟪⟫-•₃ (U-S₂₃ (ΛXZ 1)) sXB (U-S₂₃ (ΛZX 1))) (S₂₃.⟪⟫-•₃ S₂₃-X₁ sXB S₂₃-X₁)

  l85₄ : Y • XB • Yi ≈ XW
  l85₄ = begin
    Y • XB • Yi
      ≈⟨ cong ysplit (back _ yisplit) ⟩
    (Y₃ • N₂.⟪ Yi ⟫) • XB • (N₂.⟪ Y ⟫ • Y₃i)
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    Y₃ • (N₂.⟪ Yi ⟫ • XB • N₂.⟪ Y ⟫) • Y₃i
      ≈⟨ mid _ _ (trans (sym assoc) (trans (front _ V-XB) (trans assoc (trans (back _ V-Vi) right-unit)))) ⟩
    Y₃ • XB • Y₃i
      ≈⟨ A3′ ⟩
    XW ∎

  W-Yb : W • Yb • Wi ≈ X • Yb • X
  W-Yb = S₀₁.⟪⟫-≈ l85₄ (S₀₁.⟪⟫-•₃ refl refl refl) (S₀₁.⟪⟫-•₃ sX′ refl sX′)

  ----------------------------------------------------------------------
  -- The other ingredients of Canon361

  Yb-Yw : Yb • (X • Yb • X) ≈ Y
  Yb-Yw = S₀₁.⟪⟫-≈ XB-XW (S₀₁.⟪⟫-•₂ refl (S₀₁.⟪⟫-•₃ sX′ refl sX′)) (S₀₁.⟪⟫-⟪⟫ Y)

  Ybi-Ywi : Ybi • (X • Ybi • X) ≈ Yi
  Ybi-Ywi = S₀₁.⟪⟫-≈ ZXB-XWi (S₀₁.⟪⟫-•₂ refl (S₀₁.⟪⟫-•₃ sX′ refl sX′)) (S₀₁.⟪⟫-⟪⟫ Yi)

  -- (355): XB Λ is ZXB, so Yb B₁ is Ybi.
  XB-Λ : XB • Λ ≈ ZXB
  XB-Λ = trans (back _ core′₁) (trans (sym assoc) (trans (front _ eq208) left-unit))

  Yb-B₁ : Yb • B₁ ≈ Ybi
  Yb-B₁ = trans (sym (S₀₁.⟪⟫-• XB Λ)) (S₀₁.⟪⟫-cong XB-Λ)

  -- The pair step under the lower swap: Ybi passes Λ and becomes Yb.
  K : ZXB • B₁ ≈ B₁ • XB
  K = begin
    (CH • B₁ • CH • B₁) • B₁     ≈⟨ by-passoc ((□ • □ • □ • □) • □) (□ • □ • □ • (□ • □)) Eq.refl ⟩
    CH • B₁ • CH • (B₁ • B₁)     ≈⟨ back _ (back _ (trans (back _ box₃′²) right-unit)) ⟩
    CH • B₁ • CH                 ≈⟨ sym (trans (sym assoc) (trans (front _ box₃′²) left-unit)) ⟩
    B₁ • (B₁ • CH • B₁ • CH) ∎

  Ybi-Λ : Ybi • Λ ≈ Λ • Yb
  Ybi-Λ = S₀₁.⟪⟫-≈ K (S₀₁.⟪⟫-•₂ refl (S₀₁.⟪⟫-⟪⟫ Λ)) (S₀₁.⟪⟫-•₂ (S₀₁.⟪⟫-⟪⟫ Λ) refl)

  -- Λ turns Y over: Y is Yb times its copy white on wire 0, and each
  -- half is turned over.
  Yb-Λ : Yb • Λ ≈ Λ • Ybi
  Yb-Λ = S₀₁.⟪⟫-≈ (by-passoc ((□ • □ • □ • □) • □) (□ • □ • □ • □ • □) Eq.refl)
                  (S₀₁.⟪⟫-•₂ refl (S₀₁.⟪⟫-⟪⟫ Λ)) (S₀₁.⟪⟫-•₂ (S₀₁.⟪⟫-⟪⟫ Λ) refl)

  Yw-Λ : (X • Yb • X) • Λ ≈ Λ • (X • Ybi • X)
  Yw-Λ = TX.⟪⟫-≈ Yb-Λ (TX.⟪⟫-•₂ refl xΛ) (TX.⟪⟫-•₂ xΛ refl)
    where
    xΛ : TX.⟪ Λ ⟫ ≈ Λ
    xΛ = TX.⟪⟫-fix eq156

  Y-Λ : Y • Λ ≈ Λ • Yi
  Y-Λ = begin
    Y • Λ                                ≈⟨ front _ (sym Yb-Yw) ⟩
    (Yb • (X • Yb • X)) • Λ              ≈⟨ trans assoc (back _ Yw-Λ) ⟩
    Yb • (Λ • (X • Ybi • X))             ≈⟨ trans (sym assoc) (front _ Yb-Λ) ⟩
    (Λ • Ybi) • (X • Ybi • X)            ≈⟨ trans assoc (back _ Ybi-Ywi) ⟩
    Λ • Yi ∎

------------------------------------------------------------------------
-- (361)

eq361₄ : Cc ≈ Λ • Y
eq361₄ = begin
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

eq361′₄ : Cc ≈ Yi • Λ
eq361′₄ = begin
  Cc                        ≈⟨ eq361₄ ⟩
  Λ • Y                     ≈⟨ back _ (sym (trans (back _ Λ²) right-unit)) ⟩
  Λ • (Y • (Λ • Λ))         ≈⟨ back _ (trans (sym assoc) (front _ Y-Λ)) ⟩
  Λ • ((Λ • Yi) • Λ)        ≈⟨ trans (back _ assoc) (trans (sym assoc) (trans (front _ Λ²) left-unit)) ⟩
  Yi • Λ ∎

------------------------------------------------------------------------
-- (44)

private
  -- HG passes the CH from wire 2 onto wire 1: ΛH 2 passes the CH from
  -- wire 2 onto wire 0, which is the CZ of those wires between P ⊗ P
  -- ((159)).
  HG-UCH : HG • U CH ≈ U CH • HG
  HG-UCH = S₀₁.⟪⟫-≈ a-CH₂₀ (S₀₁.⟪⟫-•₂ refl uc) (S₀₁.⟪⟫-•₂ uc refl)
    where
    a-CH₂₀ : ΛH 2 • CH₂₀ ≈ CH₂₀ • ΛH 2
    a-CH₂₀ = PP↓.⟪⟫-≈ (sym eq159) (PP↓.⟪⟫-•₂ refl PP-CZ₂₀) (PP↓.⟪⟫-•₂ PP-CZ₂₀ refl)
    uc : S₀₁.⟪ CH₂₀ ⟫ ≈ U CH
    uc = S₀₁.⟪⟫-⟪⟫ (U CH)

  HG-Y : HG • Y ≈ Y • HG
  HG-Y = comm-abab HG-P₁₃CZ HG-UCH

core44₁ : (Ex ↓ • ΛH 2 • Ex ↓) • Cc ≈ Cc • (Ex ↓ • ΛH 2 • Ex ↓)
core44₁ = trans (back _ eq361₄) (trans (pass₂ HG-box₃ HG-Y) (front _ (sym eq361₄)))

------------------------------------------------------------------------
-- (43)

private
  module P = Conj {4} (PP ↓) (L-sem (PP • PP) ε Eq.refl)

  PP² : PP ↓ • PP ↓ ≈ ε
  PP² = L-sem (PP • PP) ε Eq.refl

  HC² : HC • HC ≈ ε
  HC² = conj-invol Ex² CH²

  -- (278) on four wires.
  hc-yi : HC • Yi • HC ≈ CZ ↓ • Yi • CZ ↓
  hc-yi = sym (begin
    CZ ↓ • Yi • CZ ↓
      ≈⟨ sym (trans (front _ HC²) left-unit) ⟩
    (HC • HC) • CZ ↓ • Yi • CZ ↓
      ≈⟨ by-passoc ((□ • □) • □ • □ • □) (□ • (□ • □ • □) • □) Eq.refl ⟩
    HC • (HC • CZ ↓ • Yi) • CZ ↓
      ≈⟨ back _ (front _ (eq278 0 complete₃)) ⟩
    HC • (Yi • HC • CZ ↓) • CZ ↓
      ≈⟨ by-passoc (□ • (□ • □ • □) • □) (□ • □ • □ • (□ • □)) Eq.refl ⟩
    HC • Yi • HC • (CZ ↓ • CZ ↓)
      ≈⟨ back _ (back _ (trans (back _ CZ²) right-unit)) ⟩
    HC • Yi • HC ∎)

  -- Zp: CZ • Yi • CZ ≈ B₁ • Yi, from (172) under the lower swap and B₁
  -- passing Yi ((163) and (159) moved to the box on wire 1).
  bU : U CH • B₁ ≈ B₁ • U CH
  bU = S₀₁.⟪⟫-≈ (S₁₂.⟪⟫-≈ eq163 (S₁₂.⟪⟫-•₂ (O-L CH) eq157) (S₁₂.⟪⟫-•₂ eq157 (O-L CH)))
                (S₀₁.⟪⟫-•₂ (S₀₁.⟪⟫-⟪⟫ (U CH)) refl) (S₀₁.⟪⟫-•₂ refl (S₀₁.⟪⟫-⟪⟫ (U CH)))

  bP : P₁₃ CZ • B₁ ≈ B₁ • P₁₃ CZ
  bP = S₀₁.⟪⟫-≈ (S₂₃.⟪⟫-≈ eq159 (S₂₃.⟪⟫-•₂ (O-S₂₃ CZ) eq161) (S₂₃.⟪⟫-•₂ eq161 (O-S₂₃ CZ)))
                (S₀₁.⟪⟫-•₂ (S₀₁.⟪⟫-⟪⟫ (P₁₃ CZ)) refl) (S₀₁.⟪⟫-•₂ refl (S₀₁.⟪⟫-⟪⟫ (P₁₃ CZ)))

  B₁-Yi : B₁ • Yi ≈ Yi • B₁
  B₁-Yi = comm-abab (sym bU) (sym bP)

  e172′ : CZ ↓ • Yi ≈ Yi • B₁ • CZ ↓
  e172′ = S₀₁.⟪⟫-≈ eq172 (S₀₁.⟪⟫-•₂ sCZ (S₀₁.⟪⟫-⟪⟫ Yi)) (S₀₁.⟪⟫-•₃ (S₀₁.⟪⟫-⟪⟫ Yi) refl sCZ)
    where
    sCZ : S₀₁.⟪ CZ ↓ ⟫ ≈ CZ ↓
    sCZ = L-sem (Ex • CZ • Ex) CZ Eq.refl

  Zp : CZ ↓ • Yi • CZ ↓ ≈ B₁ • Yi
  Zp = begin
    CZ ↓ • Yi • CZ ↓          ≈⟨ trans (sym assoc) (front _ e172′) ⟩
    (Yi • B₁ • CZ ↓) • CZ ↓   ≈⟨ trans assoc (back _ (trans assoc (trans (back _ CZ²) right-unit))) ⟩
    Yi • B₁                   ≈⟨ sym B₁-Yi ⟩
    B₁ • Yi ∎

  yhc : Yi • HC • Y ≈ HC • B₁
  yhc = begin
    Yi • HC • Y
      ≈⟨ sym (trans (front _ HC²) left-unit) ⟩
    (HC • HC) • Yi • HC • Y
      ≈⟨ by-passoc ((□ • □) • □ • □ • □) (□ • (□ • □ • □) • □) Eq.refl ⟩
    HC • (HC • Yi • HC) • Y
      ≈⟨ back _ (front _ (trans hc-yi Zp)) ⟩
    HC • (B₁ • Yi) • Y
      ≈⟨ back _ (trans assoc (back _ Yi-Y)) ⟩
    HC • B₁ • ε
      ≈⟨ back _ right-unit ⟩
    HC • B₁ ∎

  -- P ⊗ P on the lower pair turns the rotations over ((174)), exchanges
  -- CH and HC, and turns the box on wire 1 into HG.
  e360′ : P.⟪ Yi ⟫ ≈ Y
  e360′ = trans (sym assoc) (trans (front _ eq174) (trans assoc (trans (back _ PP²) right-unit)))

  e360 : P.⟪ Y ⟫ ≈ Yi
  e360 = conj-sym PP² e360′

  P-CH : P.⟪ CH ↓ ⟫ ≈ HC
  P-CH = L-sem (PP • CH • PP) HC Eq.refl

  hgform : Y • CH ↓ • Yi ≈ CH ↓ • HG
  hgform = P.⟪⟫-≈ yhc (P.⟪⟫-•₃ e360′ (conj-sym PP² P-CH) e360)
                      (P.⟪⟫-•₂ (conj-sym PP² P-CH) (sym ΛH₀₁-PP))

  -- The D-trick, a single merge: G times the CH from wire 1 onto wire 0
  -- is G white on wire 2 ((171ᶜ)), which passes Y — in the rotation form
  -- of G every letter meets Y on the wires 1–3 or on the triple 0 1 3.
  G-CH : G • CH ↓ ≈ °G
  G-CH = trans (back _ (sym eq171ᶜ)) (trans (sym assoc) (trans (front _ ΛH₂′²) left-unit))

  °Gform : °G ≈ N₂.⟪ Rg ⟫ • e′ • N₂.⟪ Rg⁻ ⟫ • e′
  °Gform = trans (N₂.⟪⟫-cong ΛH₂′-rot) (N₂.⟪⟫-•₄ refl ne refl ne)
    where
    ne : N₂.⟪ e′ ⟫ ≈ e′
    ne = N₂.⟪⟫-fix (sym (P₀₃-U CH (X ↑)))

  Y-°G : Y • °G ≈ °G • Y
  Y-°G = trans (back _ °Gform) (trans (pass₂ yR (pass₂ ye (pass₂ yR⁻ ye))) (front _ (sym °Gform)))
    where
    yR : Y • N₂.⟪ Rg ⟫ ≈ N₂.⟪ Rg ⟫ • Y
    yR = U₃-sem (CCXZ • (X ↑ • Rg₃ • X ↑)) ((X ↑ • Rg₃ • X ↑) • CCXZ) Eq.refl
    yR⁻ : Y • N₂.⟪ Rg⁻ ⟫ ≈ N₂.⟪ Rg⁻ ⟫ • Y
    yR⁻ = U₃-sem (CCXZ • (X ↑ • Rg⁻₃ • X ↑)) ((X ↑ • Rg⁻₃ • X ↑) • CCXZ) Eq.refl
    ye : Y • e′ ≈ e′ • Y
    ye = sym (comm-abab (sym (comm-13-03 CZ CH (evaluated Eq.refl))) (P₀₃-U CH CH))

  Y-D : Y • (G • CH ↓) ≈ (G • CH ↓) • Y
  Y-D = trans (back _ G-CH) (trans Y-°G (front _ (sym G-CH)))

  sq : (Y • CH ↓ • Yi) • (Y • CH ↓ • Yi) ≈ ε
  sq = begin
    (Y • CH ↓ • Yi) • (Y • CH ↓ • Yi)
      ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
    Y • CH ↓ • (Yi • Y) • CH ↓ • Yi
      ≈⟨ back _ (back _ (trans (front _ Yi-Y) left-unit)) ⟩
    Y • CH ↓ • CH ↓ • Yi
      ≈⟨ back _ (trans (sym assoc) (trans (front _ CH²) left-unit)) ⟩
    Y • Yi
      ≈⟨ Y-Yi ⟩
    ε ∎

  rc : (Y • G • Yi) • (Y • CH ↓ • Yi) ≈ G • CH ↓
  rc = begin
    (Y • G • Yi) • (Y • CH ↓ • Yi)
      ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
    Y • G • (Yi • Y) • CH ↓ • Yi
      ≈⟨ back _ (back _ (trans (front _ Yi-Y) left-unit)) ⟩
    Y • G • CH ↓ • Yi
      ≈⟨ by-passoc (□ • □ • □ • □) ((□ • (□ • □)) • □) Eq.refl ⟩
    (Y • (G • CH ↓)) • Yi
      ≈⟨ front _ Y-D ⟩
    ((G • CH ↓) • Y) • Yi
      ≈⟨ trans assoc (trans (back _ Y-Yi) right-unit) ⟩
    G • CH ↓ ∎

  L1′ : Y • G • Yi ≈ G • HG
  L1′ = begin
    Y • G • Yi
      ≈⟨ sym (trans (back _ sq) right-unit) ⟩
    (Y • G • Yi) • ((Y • CH ↓ • Yi) • (Y • CH ↓ • Yi))
      ≈⟨ trans (sym assoc) (front _ rc) ⟩
    (G • CH ↓) • (Y • CH ↓ • Yi)
      ≈⟨ back _ hgform ⟩
    (G • CH ↓) • (CH ↓ • HG)
      ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
    G • (CH ↓ • CH ↓) • HG
      ≈⟨ back _ (trans (front _ CH²) left-unit) ⟩
    G • HG ∎

  -- L1 for R, the H gate with its box wire on wire 2: L1′ under the swap
  -- of the wires 2 3.
  module S3 = Conj {3} (Ex ↑) (lemma-cong↑ (Ex • Ex) ε Ex²)

  sY : S₂₃.⟪ Y ⟫ ≈ Y
  sY = lemma-cong↑ (Ex ↑ • CCXZ • Ex ↑) CCXZ (S3.⟪⟫-fix (s12₃ false))

  sYi : S₂₃.⟪ Yi ⟫ ≈ Yi
  sYi = lemma-cong↑ (Ex ↑ • CCZX • Ex ↑) CCZX (S3.⟪⟫-fix (s12₃ true))

  L1 : Y • R • Yi ≈ R • HG
  L1 = S₂₃.⟪⟫-≈ L1′ (S₂₃.⟪⟫-•₃ sY (S₂₃.⟪⟫-⟪⟫ R) sYi) (S₂₃.⟪⟫-•₂ (S₂₃.⟪⟫-⟪⟫ R) S₂₃-ΛH₀₁)

  Cr-R : X ↑ ↑ • (Ex ↑ • Ex ↓) • ΛH 2 • (Ex ↓ • Ex ↑) • X ↑ ↑ ≈ R
  Cr-R = begin
    X ↑ ↑ • (Ex ↑ • Ex ↓) • ΛH 2 • (Ex ↓ • Ex ↑) • X ↑ ↑
      ≈⟨ by-passoc (□ • (□ • □) • □ • (□ • □) • □) (□ • (□ • (□ • □ • □) • □) • □) Eq.refl ⟩
    X ↑ ↑ • R • X ↑ ↑
      ≈⟨ N₂.⟪⟫-fix X₂-S₁₂ΛH₀₁ ⟩
    R ∎

  Λ-R : Λ • R ≈ R • Λ
  Λ-R = S₁₂.⟪⟫-≈ (sym HG-box₃) (S₁₂.⟪⟫-•₂ eq157 refl) (S₁₂.⟪⟫-•₂ refl eq157)

  Λ-RH : Λ • (R • HG) ≈ (R • HG) • Λ
  Λ-RH = pass₂ Λ-R (sym HG-box₃)

core43₁ : (X ↑ ↑ • (Ex ↑ • Ex ↓) • ΛH 2 • (Ex ↓ • Ex ↑) • X ↑ ↑) • (Ex ↓ • ΛH 2 • Ex ↓)
        ≈ Cc • (X ↑ ↑ • (Ex ↑ • Ex ↓) • ΛH 2 • (Ex ↓ • Ex ↑) • X ↑ ↑) • Cc
core43₁ = begin
  Cr • HG
    ≈⟨ front _ Cr-R ⟩
  R • HG
    ≈⟨ sym (trans (back _ Λ²) right-unit) ⟩
  (R • HG) • (Λ • Λ)
    ≈⟨ trans (sym assoc) (front _ (sym Λ-RH)) ⟩
  (Λ • (R • HG)) • Λ
    ≈⟨ front _ (back _ (sym L1)) ⟩
  (Λ • (Y • R • Yi)) • Λ
    ≈⟨ by-passoc ((□ • (□ • □ • □)) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
  (Λ • Y) • R • (Yi • Λ)
    ≈⟨ sym (cong eq361₄ (cong Cr-R eq361′₄)) ⟩
  Cc • Cr • Cc ∎
  where
  Cr : Circuit 4
  Cr = X ↑ ↑ • (Ex ↑ • Ex ↓) • ΛH 2 • (Ex ↓ • Ex ↑) • X ↑ ↑
