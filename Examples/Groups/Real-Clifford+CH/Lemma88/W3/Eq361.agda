------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoded double exchange on three qubits, and the cores of rules
-- (43) and (44) (Clément, Appendix E.5 at n = 3, (361), from Lemma D.2)
--
-- On three wires, between the negations, the decoded X_[0,3] X_[1,2] is
-- Cc = (Yb • B₁ • Λ) • (XW • (XB • Yb • ZXB) • XWi) with XB, ZXB the
-- rotations CCXZ, CCZX, XW, XWi the same white on wire 1, Yb the
-- rotation on wire 1, B₁ = CZ₂₀ and Λ = CZ ↑.  (361) says Cc ≈ Λ • Y
-- and Cc ≈ Yi • Λ with Y, Yi the two-wire rotations one wire up.  The
-- argument is Canon361's, its inputs from Lemma D.2: the merges on wire
-- 1 are (136)–(138) under the swap of the wires 1 2, which fixes the
-- rotations ((127)); Lemma 8.5, W • Yb • Wi ≈ X • Yb • X, is under the
-- lower swap Y • CCXZ • Yi ≈ XW — Y is Z ↑ • X ↑ times the merge of Yi
-- white on wire 2 (a two-wire evaluation), which CCXZ passes, so the
-- conjugation only sees X ↑, Z ↑ passing XW.  Then rule (44) is CH₂₀
-- passing Λ and Y, and rule (43) is Y • CH • Yi ≈ CH • CH₂₀, which is
-- P ⊗ P on the lower pair applied to Yi • HC • Y ≈ HC • CZ₂₀ — (145),
-- and CZ turning the half of Yi black on wire 0 over, (357).  Every
-- step was checked numerically first (scratchpad small-widths/t361.py).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.Lemma88.W3.Eq361
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  where

open import Data.Bool using (true ; false)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; ax ; Ex² ; X² ; Z² ; CZ² ; CH²)
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Blocks complete₂
  using (L ; U ; O ; L-sem ; U-sem ; O-L ; L-comm ; X↑-O ; Z↑-O ; by-sem₀)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (eq117 ; eq118 ; eq120 ; eq124 ; eq129 ; eq133 ; eq137 ; eq138 ; eq145 ;
         °CCZX ; °CCXZ ; CZ₂₀² ; CZ↑-CH₂₀ ; CH↑-°CCXZ ; K-W ; K-V ; Z↓-CCZX ;
         PP-CH↓ ; PP-CZ₂₀ ; module N₁ ; module N₂ ; module S↑ ; module S↓ ; module PP↓)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceFrames using (conj-swap)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Base358 using (e-zxxz)
open import Examples.Groups.Real-Clifford+CH.Lemma88.XX0312 {0} using (Cc)
open import Examples.Groups.Real-Clifford+CH.Lemma88.W3.Kit complete₂ using (s12₃ ; eq138′)
open import Examples.Groups.Real-Clifford+CH.Lemma88.W3.Box complete₂ using (core₀)

open Tools (3 VRel,_===_)
open WordAlgebra (3 VRel,_===_) using (comm-abab)

private
  module TX = Conj {3} X X²

  -- The gates.
  Λ B₁ XB ZXB XW XWi Yb Ybi Y Yi W Wi : Circuit 3
  Λ   = CZ ↑
  B₁  = CZ₂₀
  XB  = CCXZ
  ZXB = CCZX
  XW  = X ↑ • XB • X ↑
  XWi = X ↑ • ZXB • X ↑
  Yb  = Ex • XB • Ex
  Ybi = Ex • ZXB • Ex
  Y   = ΛXZ 1 ↑
  Yi  = ΛZX 1 ↑
  W   = O (ΛXZ 1)
  Wi  = O (ΛZX 1)

  pass₂ : ∀ {a u v : Circuit 3} → a • u ≈ u • a → a • v ≈ v • a → a • (u • v) ≈ (u • v) • a
  pass₂ eu ev = trans (sym assoc) (trans (front _ eu) (trans assoc (trans (back _ ev) (sym assoc))))

  Λ² : Λ • Λ ≈ ε
  Λ² = lemma-cong↑ (CZ • CZ) ε CZ²

  Z↑² : Z ↑ • Z ↑ ≈ ε
  Z↑² = lemma-cong↑ (Z • Z) ε Z²

  PP² : PP ↓ • PP ↓ ≈ ε
  PP² = L-sem (PP • PP) ε Eq.refl

  Yi-Y : Yi • Y ≈ ε
  Yi-Y = U-sem (ΛZX 1 • ΛXZ 1) ε (Evaluated.same e-zxxz)

  ----------------------------------------------------------------------
  -- Transport along the swap of the wires 1 2 and the lower swap

  S↑XB : S↑.⟪ XB ⟫ ≈ XB
  S↑XB = S↑.⟪⟫-fix (s12₃ false)

  S↑ZXB : S↑.⟪ ZXB ⟫ ≈ ZXB
  S↑ZXB = S↑.⟪⟫-fix (s12₃ true)

  S↑X : S↑.⟪ X ↑ ↑ ⟫ ≈ X ↑
  S↑X = lemma-cong↑ (Ex • X ↑ • Ex) X (by-sem₀ (Ex • X ↑ • Ex) X Eq.refl)

  S↓X : S↓.⟪ X ↑ ⟫ ≈ X
  S↓X = L-sem (Ex • X ↑ • Ex) X Eq.refl

  ----------------------------------------------------------------------
  -- The merges on wire 1 ((136)–(138) under the swap of the wires 1 2)

  XW-XB : XW • XB ≈ W
  XW-XB = S↑.⟪⟫-≈ eq138′ (S↑.⟪⟫-•₂ (S↑.⟪⟫-•₃ S↑X S↑XB S↑X) S↑XB) (O-L (ΛXZ 1))

  XB-XW : XB • XW ≈ W
  XB-XW = S↑.⟪⟫-≈ eq138 (S↑.⟪⟫-•₂ S↑XB (S↑.⟪⟫-•₃ S↑X S↑XB S↑X)) (O-L (ΛXZ 1))

  ZXB-XWi : ZXB • XWi ≈ Wi
  ZXB-XWi = S↑.⟪⟫-≈ eq137 (S↑.⟪⟫-•₂ S↑ZXB (S↑.⟪⟫-•₃ S↑X S↑ZXB S↑X)) (O-L (ΛZX 1))

  ----------------------------------------------------------------------
  -- Lemma 8.5 under the lower swap: Y • XB • Yi ≈ XW

  -- Y is Z ↑ • X ↑ times Yi white on wire 2, and Yi likewise.
  yf : Y ≈ Z ↑ • X ↑ • N₂.⟪ Yi ⟫
  yf = U-sem (ΛXZ 1) (Z • X • (X ↑ • ΛZX 1 • X ↑)) Eq.refl

  yt : Yi ≈ N₂.⟪ Y ⟫ • X ↑ • Z ↑
  yt = U-sem (ΛZX 1) ((X ↑ • ΛXZ 1 • X ↑) • X • Z) Eq.refl

  -- XB passes Yi white on wire 2.
  n2yi-form : N₂.⟪ Yi ⟫ ≈ U °CH • Z ↑ • U °CH • Z ↑
  n2yi-form = U-sem (X ↑ • ΛZX 1 • X ↑) (°CH • Z • °CH • Z) Eq.refl

  XB-U°CH : XB • U °CH ≈ U °CH • XB
  XB-U°CH = N₂.⟪⟫-≈ (sym CH↑-°CCXZ) (N₂.⟪⟫-•₂ (N₂.⟪⟫-⟪⟫ CCXZ) refl) (N₂.⟪⟫-•₂ refl (N₂.⟪⟫-⟪⟫ CCXZ))

  n2yi-xb : N₂.⟪ Yi ⟫ • XB ≈ XB • N₂.⟪ Yi ⟫
  n2yi-xb = sym (trans (back _ n2yi-form) (trans (comm-abab XB-U°CH (sym eq120)) (front _ (sym n2yi-form))))

  n2-inv : N₂.⟪ Yi ⟫ • N₂.⟪ Y ⟫ ≈ ε
  n2-inv = trans (sym (N₂.⟪⟫-• Yi Y)) (trans (N₂.⟪⟫-cong Yi-Y) N₂.⟪⟫-ε)

  -- Z ↑ passes XW.
  xw-form : XW ≈ CZ₂₀ • °CH ↓ • CZ₂₀ • °CH ↓
  xw-form = N₁.⟪⟫-•₄ e refl e refl
    where
    e : N₁.⟪ CZ₂₀ ⟫ ≈ CZ₂₀
    e = N₁.⟪⟫-fix (X↑-O CZ)

  z-xw : Z ↑ • XW ≈ XW • Z ↑
  z-xw = trans (back _ xw-form) (trans (comm-abab (Z↑-O CZ) (L-sem (Z ↑ • °CH) (°CH • Z ↑) Eq.refl))
                                       (front _ (sym xw-form)))

  l85₃ : Y • XB • Yi ≈ XW
  l85₃ = begin
    Y • XB • Yi
      ≈⟨ cong yf (back _ yt) ⟩
    (Z ↑ • X ↑ • N₂.⟪ Yi ⟫) • XB • (N₂.⟪ Y ⟫ • X ↑ • Z ↑)
      ≈⟨ by-passoc ((□ • □ • □) • □ • (□ • □ • □)) (□ • □ • (□ • □) • □ • □ • □) Eq.refl ⟩
    Z ↑ • X ↑ • (N₂.⟪ Yi ⟫ • XB) • N₂.⟪ Y ⟫ • X ↑ • Z ↑
      ≈⟨ back _ (back _ (front _ n2yi-xb)) ⟩
    Z ↑ • X ↑ • (XB • N₂.⟪ Yi ⟫) • N₂.⟪ Y ⟫ • X ↑ • Z ↑
      ≈⟨ by-passoc (□ • □ • (□ • □) • □ • □ • □) (□ • □ • □ • (□ • □) • □ • □) Eq.refl ⟩
    Z ↑ • X ↑ • XB • (N₂.⟪ Yi ⟫ • N₂.⟪ Y ⟫) • X ↑ • Z ↑
      ≈⟨ back _ (back _ (back _ (trans (front _ n2-inv) left-unit))) ⟩
    Z ↑ • X ↑ • XB • X ↑ • Z ↑
      ≈⟨ by-passoc (□ • □ • □ • □ • □) (□ • (□ • □ • □) • □) Eq.refl ⟩
    Z ↑ • XW • Z ↑
      ≈⟨ back _ (sym z-xw) ⟩
    Z ↑ • Z ↑ • XW
      ≈⟨ trans (sym assoc) (trans (front _ Z↑²) left-unit) ⟩
    XW ∎

  W-Yb : W • Yb • Wi ≈ X • Yb • X
  W-Yb = S↓.⟪⟫-≈ l85₃ (S↓.⟪⟫-•₃ refl refl refl) (S↓.⟪⟫-•₃ S↓X refl S↓X)

  ----------------------------------------------------------------------
  -- The other ingredients of Canon361

  -- Yb and its copy white on wire 0 merge into Y.
  Yb-Yw : Yb • (X • Yb • X) ≈ Y
  Yb-Yw = S↓.⟪⟫-≈ XB-XW (S↓.⟪⟫-•₂ refl (S↓.⟪⟫-•₃ S↓X refl S↓X)) (S↓.⟪⟫-⟪⟫ Y)

  Ybi-Ywi : Ybi • (X • Ybi • X) ≈ Yi
  Ybi-Ywi = S↓.⟪⟫-≈ ZXB-XWi (S↓.⟪⟫-•₂ refl (S↓.⟪⟫-•₃ S↓X refl S↓X)) (S↓.⟪⟫-⟪⟫ Yi)

  -- (355) and (317): XB Λ is ZXB, so Yb B₁ is Ybi.
  XB-Λ : XB • Λ ≈ ZXB
  XB-Λ = trans (front _ (sym eq124)) (trans assoc (trans (back _ Λ²) right-unit))

  Yb-B₁ : Yb • B₁ ≈ Ybi
  Yb-B₁ = trans (sym (S↓.⟪⟫-• XB Λ)) (S↓.⟪⟫-cong XB-Λ)

  -- The pair step under the lower swap: Ybi passes Λ and becomes Yb.
  K : ZXB • B₁ ≈ B₁ • XB
  K = begin
    (CH • CZ₂₀ • CH • CZ₂₀) • CZ₂₀     ≈⟨ by-passoc ((□ • □ • □ • □) • □) (□ • □ • □ • (□ • □)) Eq.refl ⟩
    CH • CZ₂₀ • CH • (CZ₂₀ • CZ₂₀)     ≈⟨ back _ (back _ (trans (back _ CZ₂₀²) right-unit)) ⟩
    CH • CZ₂₀ • CH                     ≈⟨ sym (trans (sym assoc) (trans (front _ CZ₂₀²) left-unit)) ⟩
    CZ₂₀ • (CZ₂₀ • CH • CZ₂₀ • CH) ∎

  Ybi-Λ : Ybi • Λ ≈ Λ • Yb
  Ybi-Λ = S↓.⟪⟫-≈ K (S↓.⟪⟫-•₂ refl (S↓.⟪⟫-⟪⟫ Λ)) (S↓.⟪⟫-•₂ (S↓.⟪⟫-⟪⟫ Λ) refl)

  -- Λ turns Y over.
  Y-Λ : Y • Λ ≈ Λ • Yi
  Y-Λ = U-sem (ΛXZ 1 • CZ) (CZ • ΛZX 1) Eq.refl

------------------------------------------------------------------------
-- (361)

eq361₃ : Cc ≈ Λ • Y
eq361₃ = begin
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

eq361′₃ : Cc ≈ Yi • Λ
eq361′₃ = begin
  Cc                        ≈⟨ eq361₃ ⟩
  Λ • Y                     ≈⟨ back _ (sym (trans (back _ Λ²) right-unit)) ⟩
  Λ • (Y • (Λ • Λ))         ≈⟨ back _ (trans (sym assoc) (front _ Y-Λ)) ⟩
  Λ • ((Λ • Yi) • Λ)        ≈⟨ trans (back _ assoc) (trans (sym assoc) (trans (front _ Λ²) left-unit)) ⟩
  Yi • Λ ∎

------------------------------------------------------------------------
-- (44)

core44₀ : (Ex ↓ • ΛH 1 • Ex ↓) • Cc ≈ Cc • (Ex ↓ • ΛH 1 • Ex ↓)
core44₀ = trans (back _ eq361₃) (trans (pass₂ (sym CZ↑-CH₂₀) p₂) (front _ (sym eq361₃)))
  where
  yform : Y ≈ Z ↑ • CH ↑ • Z ↑ • CH ↑
  yform = U-sem (ΛXZ 1) (Z • CH • Z • CH) Eq.refl
  p₂ : CH₂₀ • Y ≈ Y • CH₂₀
  p₂ = trans (back _ yform) (trans (comm-abab (sym (Z↑-O CH)) (sym eq133)) (front _ (sym yform)))

------------------------------------------------------------------------
-- (43)

private
  ch↓ : (Ex ↑ • Ex ↓) • CH ↑ • (Ex ↓ • Ex ↑) ≈ CH ↓
  ch↓ = trans (by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl)
              (conj-sym (lemma-cong↑ (Ex • Ex) ε Ex²) (O-L CH))

  Cr₀ : Circuit 3
  Cr₀ = X ↑ ↑ • (Ex ↑ • Ex ↓) • ΛH 1 • (Ex ↓ • Ex ↑) • X ↑ ↑

  cr : Cr₀ ≈ CH ↓
  cr = begin
    X ↑ ↑ • (Ex ↑ • Ex ↓) • CH ↑ • (Ex ↓ • Ex ↑) • X ↑ ↑
      ≈⟨ by-passoc (□ • (□ • □) • □ • (□ • □) • □) (□ • ((□ • □) • □ • (□ • □)) • □) Eq.refl ⟩
    X ↑ ↑ • ((Ex ↑ • Ex ↓) • CH ↑ • (Ex ↓ • Ex ↑)) • X ↑ ↑
      ≈⟨ mid _ _ ch↓ ⟩
    X ↑ ↑ • CH • X ↑ ↑
      ≈⟨ N₂.⟪⟫-fix (sym (L-comm CH X)) ⟩
    CH ∎

  HC² : HC • HC ≈ ε
  HC² = conj-invol Ex² CH²

  -- (278) on three wires: (145).
  hc-yi : HC • Yi • HC ≈ CZ ↓ • Yi • CZ ↓
  hc-yi = sym (begin
    CZ ↓ • Yi • CZ ↓
      ≈⟨ sym (trans (front _ HC²) left-unit) ⟩
    (HC • HC) • CZ ↓ • Yi • CZ ↓
      ≈⟨ by-passoc ((□ • □) • □ • □ • □) (□ • (□ • □ • □) • □) Eq.refl ⟩
    HC • (HC • CZ ↓ • Yi) • CZ ↓
      ≈⟨ back _ (front _ eq145) ⟩
    HC • (Yi • HC • CZ ↓) • CZ ↓
      ≈⟨ by-passoc (□ • (□ • □ • □) • □) (□ • □ • □ • (□ • □)) Eq.refl ⟩
    HC • Yi • HC • (CZ ↓ • CZ ↓)
      ≈⟨ back _ (back _ (trans (back _ CZ²) right-unit)) ⟩
    HC • Yi • HC ∎)

  -- Zp: CZ • Yi • CZ ≈ B₁ • Yi, from (357) on the halves of Yi.
  CZ-Ex : CZ ↓ • Ex ≈ Ex • CZ ↓
  CZ-Ex = L-sem (CZ • Ex) (Ex • CZ) Eq.refl

  CZ-Ybi : CZ ↓ • Ybi • CZ ↓ ≈ Yb
  CZ-Ybi = trans (conj-swap CZ-Ex ZXB) (mid _ _ K-W)

  CZ-Yb : CZ ↓ • Yb • CZ ↓ ≈ Ybi
  CZ-Yb = trans (conj-swap CZ-Ex XB) (mid _ _ K-V)

  X-CZ : X • (CZ ↓ • Z ↑) • X ≈ CZ ↓
  X-CZ = L-sem (X • (CZ • Z ↑) • X) CZ Eq.refl

  X-ZCZ : X • (Z ↑ • CZ ↓) • X ≈ CZ ↓
  X-ZCZ = L-sem (X • (Z ↑ • CZ) • X) CZ Eq.refl

  zx-Z : Z • ZXB • Z ≈ XB
  zx-Z = trans (sym assoc) (trans (front _ Z↓-CCZX) (trans assoc (trans (back _ Z²) right-unit)))

  Z-Ybi : Z ↑ • Ybi • Z ↑ ≈ Yb
  Z-Ybi = begin
    Z ↑ • (Ex • ZXB • Ex) • Z ↑      ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
    (Z ↑ • Ex) • ZXB • (Ex • Z ↑)    ≈⟨ cong ze (back _ ez) ⟩
    (Ex • Z) • ZXB • (Z • Ex)        ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    Ex • (Z • ZXB • Z) • Ex          ≈⟨ mid _ _ zx-Z ⟩
    Ex • XB • Ex ∎
    where
    ze : Z ↑ • Ex ≈ Ex • Z
    ze = L-sem (Z ↑ • Ex) (Ex • Z) Eq.refl
    ez : Ex • Z ↑ ≈ Z • Ex
    ez = L-sem (Ex • Z ↑) (Z • Ex) Eq.refl

  CZ-Ywi : CZ ↓ • (X • Ybi • X) • CZ ↓ ≈ X • Ybi • X
  CZ-Ywi = begin
    CZ ↓ • TX.⟪ Ybi ⟫ • CZ ↓
      ≈⟨ sym (TX.⟪⟫-•₃ X-CZ refl X-ZCZ) ⟩
    TX.⟪ (CZ ↓ • Z ↑) • Ybi • (Z ↑ • CZ ↓) ⟫
      ≈⟨ TX.⟪⟫-cong (by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl) ⟩
    TX.⟪ CZ ↓ • (Z ↑ • Ybi • Z ↑) • CZ ↓ ⟫
      ≈⟨ TX.⟪⟫-cong (trans (mid _ _ Z-Ybi) CZ-Yb) ⟩
    TX.⟪ Ybi ⟫ ∎

  B₁-Yb : B₁ ≈ Yb • Yb
  B₁-Yb = trans (S↓.⟪⟫-cong core₀) (S↓.⟪⟫-• XB XB)

  Yb-Ybi : Yb • Ybi ≈ ε
  Yb-Ybi = trans (sym (S↓.⟪⟫-• XB ZXB)) (trans (S↓.⟪⟫-cong eq118) S↓.⟪⟫-ε)

  Zp : CZ ↓ • Yi • CZ ↓ ≈ B₁ • Yi
  Zp = begin
    CZ ↓ • Yi • CZ ↓
      ≈⟨ mid _ _ (sym Ybi-Ywi) ⟩
    CZ ↓ • (Ybi • (X • Ybi • X)) • CZ ↓
      ≈⟨ Conj.⟪⟫-• (CZ ↓) CZ² Ybi (X • Ybi • X) ⟩
    (CZ ↓ • Ybi • CZ ↓) • (CZ ↓ • (X • Ybi • X) • CZ ↓)
      ≈⟨ cong CZ-Ybi CZ-Ywi ⟩
    Yb • (X • Ybi • X)
      ≈⟨ back _ (sym (trans (front _ Yb-Ybi) left-unit)) ⟩
    Yb • ((Yb • Ybi) • (X • Ybi • X))
      ≈⟨ by-passoc (□ • ((□ • □) • □)) ((□ • □) • (□ • □)) Eq.refl ⟩
    (Yb • Yb) • (Ybi • (X • Ybi • X))
      ≈⟨ cong (sym B₁-Yb) Ybi-Ywi ⟩
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

  -- P ⊗ P on the lower pair turns the rotations over ((129)) and
  -- exchanges CH and HC, CZ₂₀ and CH₂₀.
  e360′ : PP↓.⟪ Yi ⟫ ≈ Y
  e360′ = trans (sym assoc) (trans (front _ eq129) (trans assoc (trans (back _ PP²) right-unit)))

  e360 : PP↓.⟪ Y ⟫ ≈ Yi
  e360 = conj-sym PP² e360′

  hgform : Y • CH ↓ • Yi ≈ CH ↓ • CH₂₀
  hgform = PP↓.⟪⟫-≈ yhc (PP↓.⟪⟫-•₃ e360′ (conj-sym PP² PP-CH↓) e360)
                        (PP↓.⟪⟫-•₂ (conj-sym PP² PP-CH↓) PP-CZ₂₀)

  Λ-CH : Λ • CH ↓ ≈ CH ↓ • Λ
  Λ-CH = ax comm-CZ↑-CH↓

core43₀ : Cr₀ • (Ex ↓ • ΛH 1 • Ex ↓) ≈ Cc • Cr₀ • Cc
core43₀ = sym (begin
  Cc • Cr₀ • Cc
    ≈⟨ cong eq361₃ (cong cr eq361′₃) ⟩
  (Λ • Y) • CH ↓ • (Yi • Λ)
    ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
  Λ • (Y • CH ↓ • Yi) • Λ
    ≈⟨ mid _ _ hgform ⟩
  Λ • (CH ↓ • CH₂₀) • Λ
    ≈⟨ trans (sym assoc) (front _ (pass₂ Λ-CH CZ↑-CH₂₀)) ⟩
  ((CH ↓ • CH₂₀) • Λ) • Λ
    ≈⟨ trans assoc (trans (back _ Λ²) right-unit) ⟩
  CH ↓ • CH₂₀
    ≈⟨ front _ (sym cr) ⟩
  Cr₀ • CH₂₀ ∎)
