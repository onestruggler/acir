------------------------------------------------------------------------
-- Presentations of groups
--
-- The canonical form of rule (43) of Figure 8 (Clément, Lemma 8.8)
--
-- At width 5 + k, between the negations of the wires 2 …, rule (43)
-- says Cr • S ≈ C • Cr • C (`core43`): S is the H gate HG (H on wire 0,
-- box wire 1), Cr the H gate R with its box wire on wire 2 (X on that
-- wire passes it), and C the decoded X_[0,3] X_[1,2], which is Λ • Y
-- ((361)) and Yi • Λ (`eq361′`), with Λ the box and Y, Yi the rotations
-- on wire 1 with wire 0 idle.  Λ passes R and HG ((338) with x = y), so
-- the rule is
--
--   Y • R • Yi ≈ R • HG          (`L1`).
--
-- The D-trick: the CH from wire 1 onto wire 0 is R over every colouring
-- of the wires 3 … (Canon40's CH₂-∏ under the swap of the wires 1 2),
-- and every colouring but the black one passes Y, so Y passes R • CH;
-- then L1 is `hgform`, Y • CH • Yi ≈ CH • HG.  That is, between P ⊗ P on
-- the wires 0 1 (which turns Y over, (360), GeneralN.ZX360), Yi • HC •
-- Y ≈ HC • B₁: HC Yi HC = CZ Yi CZ by (278), and CZ Yi CZ = B₁ Yi
-- (`Zp`: the CZ turns the half of Yi black on wire 0 over, (357), and
-- fixes the white half).  A coloured R passes Y because, by `hgform`
-- under the swap of the wires 1 2, it is CH₂ • V • CH₂ • Vi with V the
-- rotation on wire 2, wire 0 idle: CH₂ passes Y (`N2′`), and Y and V,
-- each the merge of two placed rotations over the colours of wire 0
-- ((354)), commute pair by pair by (352) placed (RotAnywhere), the
-- white top wire separating them.  Every step was checked numerically
-- first (scratchpad t43a.py, t360.py; r4x/plan43d.py).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.Canon43
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Nat using (ℕ ; suc ; s≤s ; z≤n)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (Σ ; _,_)
open import Data.Vec using ([] ; _∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (allBits ; lookupℕ)
open import Examples.Groups.Real-Clifford+CH.Encoding using (∏)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (perm)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; Ex² ; X² ; S-X↑ ; S-Z↑ ; S-CZ ; ax)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Figure13 complete₂ using (eq111)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃ using (L₃-sem ; module S₁₂)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB ; negs² ; sdS ; sd-target)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon ; pl)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (place)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (low-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.LocalPlace using (local-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (placeAt ; placeAt-place ; placeAt-step ; X-step)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceCalc using (placeAt-zero)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col ; Hg)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃ using (Completes ; SymAt ; eqSymAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CanonN complete₂ complete₃ using (canonN)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZXPass complete₂ complete₃ using (Complete ; eq278 ; eq280)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX360 complete₂ complete₃ using (eq360 ; eq360′ ; sem-zx-xz ; sem-xz-zx)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX353 complete₂ complete₃ using (allT ; ∏-conj ; ∏-cong)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX354 complete₂ complete₃ using (eq354₁′)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX355 complete₂ complete₃ using (eq355)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX356 complete₂ complete₃ using (eq357 ; eq357′ ; zx-Z)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon31 complete₂ complete₃ using (K1)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon361 complete₂ complete₃ using (eq361)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box338 complete₂ complete₃ using (module Carry)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Colours complete₂ complete₃ using (conj-swap)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box338Eq complete₂ complete₃ using (module XY)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon40 complete₂ complete₃ using (HG-CH₂ ; Hcol ; CH₂-∏′)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotAnywhere complete₂ complete₃ using (rot-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.MergeGen using (pass-last′)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon38 complete₂ complete₃ using (k₀)
import Examples.Groups.Real-Clifford+CH.Lemma88.Invol as Invol
open import Examples.Groups.Real-Clifford+CH.Lemma88.XX0312 using (Cc)

-- The network carrying wire 2 to wire 0, and where it sends wire 2, at a
-- variable width.
perm-k₀ : ∀ {n} → perm {₄₊ n} k₀ ⟨$⟩ʳ sF (sF 0F) ≡ 0F
perm-k₀ = Eq.refl

private
  white : ∀ {n} (c : Bits n) → c ≢ replicate n true → Σ (Fin n) (λ j → lookupℕ (toℕ j) c ≡ false)
  white []          ne = ⊥-elim (ne Eq.refl)
  white (false ∷ c) ne = 0F , Eq.refl
  white (true ∷ c)  ne with white c (λ e → ne (Eq.cong (true ∷_) e))
  ... | j , e = sF j , e

  lk-ones : ∀ {n} (j : Fin n) → lookupℕ (toℕ j) (replicate n true) ≡ true
  lk-ones 0F     = Eq.refl
  lk-ones (sF j) = lk-ones j

  tf : true ≢ false
  tf ()

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    N : ℕ
    N = ₁₊ (₄₊ k)

    completes : Completes (₁₊ k)
    completes j≤ = below (s≤s (s≤s (s≤s (s≤s j≤))))

    canon : Canon (₂₊ k)
    canon = canonN k completes

    complete₁ₖ : Complete (₁₊ k)
    complete₁ₖ = completes ≤-refl

    symAt : SymAt (₁₊ k)
    symAt = eqSymAt (₁₊ k) completes

    module I = Invol canon complete₂

  open Tools (N VRel,_===_)
  open XY k below using (X-Hg ; S-ΛH ; eq338xy)

  private
    ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
    ≡→≈ Eq.refl = refl

    both : ∀ {p p′ q q′ : Circuit N} → p ≈ p′ → q ≈ q′ → p • q ≈ q • p → p′ • q′ ≈ q′ • p′
    both ep eq e = trans (sym (cong ep eq)) (trans e (cong eq ep))

    pass₂ : ∀ {a u v : Circuit N} → a • u ≈ u • a → a • v ≈ v • a → a • (u • v) ≈ (u • v) • a
    pass₂ eu ev = trans (sym assoc) (trans (front _ eu) (trans assoc (trans (back _ ev) (sym assoc))))

    passL : ∀ {a b y : Circuit N} → a • y ≈ y • a → b • y ≈ y • b → (a • b) • y ≈ y • (a • b)
    passL ea eb = trans assoc (trans (back _ eb) (trans (sym assoc) (trans (front _ ea) assoc)))

    fixc : ∀ {s u : Circuit N} → s • u ≈ u • s → s • s ≈ ε → s • u • s ≈ u
    fixc e s² = trans (sym assoc) (trans (front _ e) (trans assoc (trans (back _ s²) right-unit)))

    Ex↑² : Ex ↑ • Ex ↑ ≈ ε
    Ex↑² = lemma-cong↑ _ _ Ex²

    X↑↑² : X ↑ ↑ • X ↑ ↑ ≈ ε
    X↑↑² = lemma-cong↑ _ _ (lemma-cong↑ _ _ X²)

    CZ² : CZ ↓ • CZ ↓ ≈ ε
    CZ² = ax order-CZ

    CH² : CH ↓ • CH ↓ ≈ ε
    CH² = ax order-CH

    module S₀ = Conj {N} Ex Ex²
    module TX = Conj {N} X X²
    module P  = Conj {N} (PP ↓) eq111
    module C₁₂ = Carry {N} (Ex ↑) Ex↑²

  ----------------------------------------------------------------------
  -- The gates

  Λ HG R Y Yi Yb Ybi Yw Ywi B₁ : Circuit N
  Λ   = Λ□ (₄₊ k)
  HG  = Hg (₂₊ k)
  R   = Ex ↑ • HG • Ex ↑
  Y   = ΛXZ (₃₊ k) ↑
  Yi  = ΛZX (₃₊ k) ↑
  Yb  = Ex • ΛXZ (₄₊ k) • Ex
  Ybi = Ex • ΛZX (₄₊ k) • Ex
  Yw  = X • Yb • X
  Ywi = X • Ybi • X
  B₁  = Ex • Λ • Ex

  private
    Λ² : Λ • Λ ≈ ε
    Λ² = Canon.invol canon

    HG² : HG • HG ≈ ε
    HG² = conj-invol eq111 (conj-invol Ex² Λ²)

    R² : R • R ≈ ε
    R² = conj-invol Ex↑² HG²

    Yi-Y : Yi • Y ≈ ε
    Yi-Y = lemma-cong↑ _ _ (complete₁ₖ (sem-zx-xz (₁₊ k)))

    Y-Yi : Y • Yi ≈ ε
    Y-Yi = lemma-cong↑ _ _ (complete₁ₖ (sem-xz-zx (₁₊ k)))

    Yb-Ybi : Yb • Ybi ≈ ε
    Yb-Ybi = trans (sym (S₀.⟪⟫-• (ΛXZ (₄₊ k)) (ΛZX (₄₊ k)))) (trans (S₀.⟪⟫-cong I.xz-zx) S₀.⟪⟫-ε)

    ------------------------------------------------------------------
    -- Y as the merge of its halves black and white on wire 0 ((354)
    -- under the swap; as in Canon361)

    place-Y : ∀ (u : Circuit (₄₊ k)) → Ex • u ↑ • Ex ≈ placeAt 1 u
    place-Y u = sym (trans (placeAt-step 0 u (s≤s z≤n)) (back _ (front _ (placeAt-zero u))))

    halves : ∀ β → S₀.⟪ rot β ⟫ • (X • S₀.⟪ rot β ⟫ • X) ≈ rot {₁₊ k} β ↑
    halves β = S₀.⟪⟫-≈ (eq354₁′ k below β) (S₀.⟪⟫-•₂ refl (S₀.⟪⟫-•₃ S-X↑ refl S-X↑))
                 (trans (S₀.⟪⟫-cong (≡→≈ (Eq.sym (placeAt-place 1 (rot {₁₊ k} β)))))
                        (conj-sym Ex² (place-Y (rot {₁₊ k} β))))

    Yb-Yw : Yb • Yw ≈ Y
    Yb-Yw = halves false

    Ybi-Ywi : Ybi • Ywi ≈ Yi
    Ybi-Ywi = halves true

    ------------------------------------------------------------------
    -- Λ turns Y over: Y • Λ ≈ Λ • Yi (Canon31.K1 under the swap)

    eb : col (true ∷ true ∷ replicate (₃₊ k) true) B₁ ≈ B₁
    eb = trans (≡→≈ (Eq.cong (λ z → z • B₁ • z) (allT N))) (trans left-unit right-unit)

    Yb-Λ : Yb • Λ ≈ Λ • Ybi
    Yb-Λ = S₀.⟪⟫-≈ K (S₀.⟪⟫-•₂ refl (S₀.⟪⟫-⟪⟫ Λ)) (S₀.⟪⟫-•₂ (S₀.⟪⟫-⟪⟫ Λ) refl)
      where
      K : ΛXZ (₄₊ k) • B₁ ≈ B₁ • ΛZX (₄₊ k)
      K = trans (back _ (sym eb)) (trans (K1 k below false true true) (front _ eb))

    XΛX : X • Λ • X ≈ Λ
    XΛX = fixc (Canon.x-box canon) X²

    Yw-Λ : Yw • Λ ≈ Λ • Ywi
    Yw-Λ = TX.⟪⟫-≈ Yb-Λ (TX.⟪⟫-•₂ refl XΛX) (TX.⟪⟫-•₂ XΛX refl)

    Y-Λ : Y • Λ ≈ Λ • Yi
    Y-Λ = begin
      Y • Λ                ≈⟨ front _ (sym Yb-Yw) ⟩
      (Yb • Yw) • Λ        ≈⟨ trans assoc (back _ Yw-Λ) ⟩
      Yb • (Λ • Ywi)       ≈⟨ trans (sym assoc) (front _ Yb-Λ) ⟩
      (Λ • Ybi) • Ywi      ≈⟨ trans assoc (back _ Ybi-Ywi) ⟩
      Λ • Yi ∎

  eq361′ : Cc {₂₊ k} ≈ Yi • Λ
  eq361′ = begin
    Cc                        ≈⟨ eq361 k below ⟩
    Λ • Y                     ≈⟨ back _ (sym (trans (back _ Λ²) right-unit)) ⟩
    Λ • (Y • (Λ • Λ))         ≈⟨ back _ (trans (sym assoc) (front _ Y-Λ)) ⟩
    Λ • ((Λ • Yi) • Λ)        ≈⟨ trans (back _ assoc) (trans (sym assoc) (trans (front _ Λ²) left-unit)) ⟩
    Yi • Λ ∎

  private
    ------------------------------------------------------------------
    -- Zp: CZ • Yi • CZ ≈ B₁ • Yi

    CZ-Ex : CZ ↓ • Ex ≈ Ex • CZ ↓
    CZ-Ex = conj-comm Ex² S-CZ

    CZ-Ybi : CZ ↓ • Ybi • CZ ↓ ≈ Yb
    CZ-Ybi = trans (conj-swap CZ-Ex (ΛZX (₄₊ k))) (mid _ _ (eq357 k below))

    CZ-Yb : CZ ↓ • Yb • CZ ↓ ≈ Ybi
    CZ-Yb = trans (conj-swap CZ-Ex (ΛXZ (₄₊ k))) (mid _ _ (eq357′ k below))

    -- X on wire 0 around the CZ is the CZ and Z on wire 1.
    X-CZ : X • (CZ ↓ • Z ↑) • X ≈ CZ ↓
    X-CZ = L₃-sem (X • (CZ • Z ↑) • X) CZ Eq.refl

    X-ZCZ : X • (Z ↑ • CZ ↓) • X ≈ CZ ↓
    X-ZCZ = L₃-sem (X • (Z ↑ • CZ) • X) CZ Eq.refl

    -- A conjugation by d moved inside a conjugation by c: c • (d w d) • c
    -- = d • (c′ w c′) • d when d c d = c′.
    sw : ∀ {c d c′ : Circuit N} → d • d ≈ ε → d • c • d ≈ c′ → ∀ w → c • (d • w • d) • c ≈ d • (c′ • w • c′) • d
    sw {c} {d} {c′} d² h w = begin
      c • (d • w • d) • c    ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (c • d) • w • (d • c)  ≈⟨ cong (conj-comm d² h) (back _ (sym (conj-comm d² (conj-sym d² h)))) ⟩
      (d • c′) • w • (c′ • d) ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
      d • (c′ • w • c′) • d ∎

    Z-Ybi : Z ↑ • Ybi • Z ↑ ≈ Yb
    Z-Ybi = trans (sw Ex² S-Z↑ (ΛZX (₄₊ k))) (mid _ _ (zx-Z k below))

    CZ-Ywi : CZ ↓ • Ywi • CZ ↓ ≈ Ywi
    CZ-Ywi = begin
      CZ ↓ • TX.⟪ Ybi ⟫ • CZ ↓
        ≈⟨ sym (TX.⟪⟫-•₃ X-CZ refl X-ZCZ) ⟩
      TX.⟪ (CZ ↓ • Z ↑) • Ybi • (Z ↑ • CZ ↓) ⟫
        ≈⟨ TX.⟪⟫-cong (by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl) ⟩
      TX.⟪ CZ ↓ • (Z ↑ • Ybi • Z ↑) • CZ ↓ ⟫
        ≈⟨ TX.⟪⟫-cong (trans (mid _ _ Z-Ybi) CZ-Yb) ⟩
      TX.⟪ Ybi ⟫ ∎

    B₁-Yb : B₁ ≈ Yb • Yb
    B₁-Yb = trans (S₀.⟪⟫-cong (eq355 k below)) (S₀.⟪⟫-• (ΛXZ (₄₊ k)) (ΛXZ (₄₊ k)))

    Zp : CZ ↓ • Yi • CZ ↓ ≈ B₁ • Yi
    Zp = begin
      CZ ↓ • Yi • CZ ↓
        ≈⟨ mid _ _ (sym Ybi-Ywi) ⟩
      CZ ↓ • (Ybi • Ywi) • CZ ↓
        ≈⟨ S-split ⟩
      (CZ ↓ • Ybi • CZ ↓) • (CZ ↓ • Ywi • CZ ↓)
        ≈⟨ cong CZ-Ybi CZ-Ywi ⟩
      Yb • Ywi
        ≈⟨ back _ (sym (trans (front _ Yb-Ybi) left-unit)) ⟩
      Yb • ((Yb • Ybi) • Ywi)
        ≈⟨ by-passoc (□ • ((□ • □) • □)) ((□ • □) • (□ • □)) Eq.refl ⟩
      (Yb • Yb) • (Ybi • Ywi)
        ≈⟨ cong (sym B₁-Yb) Ybi-Ywi ⟩
      B₁ • Yi ∎
      where
      S-split : CZ ↓ • (Ybi • Ywi) • CZ ↓ ≈ (CZ ↓ • Ybi • CZ ↓) • (CZ ↓ • Ywi • CZ ↓)
      S-split = Conj.⟪⟫-• (CZ ↓) CZ² Ybi Ywi

    ------------------------------------------------------------------
    -- HgForm: Y • CH • Yi ≈ CH • HG, between P ⊗ P

    hc-yi : HC • Yi • HC ≈ CZ ↓ • Yi • CZ ↓
    hc-yi = sym (begin
      CZ ↓ • Yi • CZ ↓
        ≈⟨ sym (trans (front _ HC²) left-unit) ⟩
      (HC • HC) • CZ ↓ • Yi • CZ ↓
        ≈⟨ by-passoc ((□ • □) • □ • □ • □) (□ • (□ • □ • □) • □) Eq.refl ⟩
      HC • (HC • CZ ↓ • Yi) • CZ ↓
        ≈⟨ back _ (front _ (eq278 (₁₊ k) complete₁ₖ)) ⟩
      HC • (Yi • HC • CZ ↓) • CZ ↓
        ≈⟨ by-passoc (□ • (□ • □ • □) • □) (□ • □ • □ • (□ • □)) Eq.refl ⟩
      HC • Yi • HC • (CZ ↓ • CZ ↓)
        ≈⟨ back _ (back _ (trans (back _ CZ²) right-unit)) ⟩
      HC • Yi • HC ∎)
      where
      HC² : HC • HC ≈ ε
      HC² = conj-invol Ex² CH²

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
      where
      HC² : HC • HC ≈ ε
      HC² = conj-invol Ex² CH²

    P-CH : P.⟪ CH ↓ ⟫ ≈ HC
    P-CH = L₃-sem (PP • CH • PP) HC Eq.refl

  hgform : Y • CH ↓ • Yi ≈ CH ↓ • HG
  hgform = P.⟪⟫-≈ yhc (P.⟪⟫-•₃ (eq360′ (₁₊ k) complete₁ₖ) (conj-sym eq111 P-CH) (eq360 (₁₊ k) complete₁ₖ))
                      (P.⟪⟫-•₂ (conj-sym eq111 P-CH) refl)

  private
    ------------------------------------------------------------------
    -- N2′: the CH from wire 2 onto wire 0 passes Y

    CH₂ : Circuit N
    CH₂ = S₁₂.⟪ CH ⟫

    -- The CH from the box wire onto the idle wire below passes the box
    -- one wire up ((280), with (274) around it).
    CH-Λ↑ : CH • Λ□ (₃₊ k) ↑ ≈ Λ□ (₃₊ k) ↑ • CH
    CH-Λ↑ = trans (front _ (sym (unconj Ex²)))
                  (trans (lp ex (lp (eq280 (₁₊ k) complete₁ₖ) ex)) (back _ (unconj Ex²)))
      where
      L : Circuit N
      L = Λ□ (₃₊ k) ↑
      ex : Ex • L ≈ L • Ex
      ex = sym (conj-comm Ex² (Canon.wire274 canon))
      lp : ∀ {x y : Circuit N} → x • L ≈ L • x → y • L ≈ L • y → (x • y) • L ≈ L • (x • y)
      lp ex ey = trans assoc (trans (back _ ey) (trans (sym assoc) (trans (front _ ex) assoc)))

    CH₂-B : CH₂ • (Ex ↑ • Λ□ (₃₊ k) ↑ • Ex ↑) ≈ (Ex ↑ • Λ□ (₃₊ k) ↑ • Ex ↑) • CH₂
    CH₂-B = C₁₂.carry refl refl CH-Λ↑

    CH₂-CH↑ : CH₂ • CH ↑ ≈ CH ↑ • CH₂
    CH₂-CH↑ = L₃-sem ((Ex ↑ • CH • Ex ↑) • CH ↑) (CH ↑ • (Ex ↑ • CH • Ex ↑)) Eq.refl

    N2′ : CH₂ • Y ≈ Y • CH₂
    N2′ = pass₂ CH₂-B (pass₂ CH₂-CH↑ (pass₂ CH₂-B CH₂-CH↑))

    ------------------------------------------------------------------
    -- R coloured on the wires 3 … as a word in CH₂ and the rotation V
    -- on wire 2 (hgform under the swap of the wires 1 2)

    V Vi : Circuit N
    V  = S₁₂.⟪ Y ⟫
    Vi = S₁₂.⟪ Yi ⟫

    CH₂² : CH₂ • CH₂ ≈ ε
    CH₂² = conj-invol Ex↑² CH²

    hg₂ : V • CH₂ • Vi ≈ CH₂ • R
    hg₂ = S₁₂.⟪⟫-≈ hgform (S₁₂.⟪⟫-•₃ refl refl refl) (S₁₂.⟪⟫-•₂ refl refl)

    R-form : R ≈ CH₂ • V • CH₂ • Vi
    R-form = begin
      R                              ≈⟨ sym (trans (sym assoc) (trans (front _ CH₂²) left-unit)) ⟩
      CH₂ • (CH₂ • R)                ≈⟨ back _ (sym hg₂) ⟩
      CH₂ • V • CH₂ • Vi ∎

    -- A colouring of the wires 3 … passes CH₂.
    colCH₂ : ∀ (c : Bits (₂₊ k)) → col (true ∷ true ∷ true ∷ c) CH₂ ≈ CH₂
    colCH₂ c = fixc′ (local-comm {k = 3} (Ex ↑ • CH • Ex ↑) (negsB c)) (negs² (true ∷ true ∷ true ∷ c))
      where
      fixc′ : ∀ {s u : Circuit N} → u • s ≈ s • u → s • s ≈ ε → s • u • s ≈ u
      fixc′ e s² = fixc (sym e) s²

    col-• : ∀ (s : Bits N) a b → col s (a • b) ≈ col s a • col s b
    col-• s a b = sym (begin
      (negsB s • a • negsB s) • (negsB s • b • negsB s)
        ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • ((□ • □) • □ • □)) Eq.refl ⟩
      negsB s • a • ((negsB s • negsB s) • b • negsB s)
        ≈⟨ back _ (back _ (trans (front _ (negs² s)) left-unit)) ⟩
      negsB s • a • (b • negsB s)
        ≈⟨ back _ (sym assoc) ⟩
      negsB s • (a • b) • negsB s ∎)

    ------------------------------------------------------------------
    -- Y and a coloured V commute: each is the merge of two placed
    -- rotations over the colours of wire 0, and (352) placed applies

    ones₄ : Bits (₄₊ k)
    ones₄ = replicate (₄₊ k) true

    Ypl : ∀ (a : Bool) (β : Bool) → Circuit N
    Ypl a β = place (sdS 1) (a ∷ ones₄) (rot β)

    Vpl : ∀ (a : Bool) (c : Bits (₂₊ k)) (β : Bool) → Circuit N
    Vpl a c β = place k₀ (a ∷ true ∷ true ∷ c) (rot β)

    yv : ∀ a b α β (c : Bits (₂₊ k)) → c ≢ replicate (₂₊ k) true →
         Ypl a α • Vpl b c β ≈ Vpl b c β • Ypl a α
    yv a b α β c ne with white c ne
    ... | j , cj = rot-comm k below α β (sdS 1) k₀ (sF 0F) (sF (sF 0F)) (sd-target (sF 0F)) perm-k₀
                            (a ∷ ones₄) (b ∷ true ∷ true ∷ c) Eq.refl Eq.refl
                            (sF (sF (sF j))) (λ ()) (λ ()) sep
      where
      sep : lookupℕ (toℕ (sF (sF (sF j)))) (a ∷ ones₄) ≢ lookupℕ (toℕ (sF (sF (sF j)))) (b ∷ true ∷ true ∷ c)
      sep e = tf (Eq.trans (Eq.sym (lk-ones {₄₊ k} (sF (sF j)))) (Eq.trans e cj))

    -- The placements.
    ones-col : ∀ (w : Circuit N) → col (true ∷ ones₄) w ≈ w
    ones-col w = trans (≡→≈ (Eq.cong (λ z → z • w • z) (allT N))) (trans left-unit right-unit)

    white-col : ∀ (w : Circuit N) → col (false ∷ ones₄) w ≈ X • w • X
    white-col w = trans (≡→≈ (Eq.cong (λ z → (X • z ↑) • w • (X • z ↑)) (allT (₄₊ k))))
                        (cong right-unit (back _ right-unit))

    pl-1 : ∀ (g : Circuit N) → pl (sdS 1) g ≈ Ex • g • Ex
    pl-1 g = cong right-unit (back _ left-unit)

    Yb-pl : ∀ β → S₀.⟪ rot β ⟫ ≈ Ypl true β
    Yb-pl β = sym (trans (ones-col (pl (sdS 1) (rot β))) (pl-1 (rot β)))

    Yw-pl : ∀ β → X • S₀.⟪ rot β ⟫ • X ≈ Ypl false β
    Yw-pl β = sym (trans (white-col (pl (sdS 1) (rot β))) (mid _ _ (pl-1 (rot β))))

    Y-pl : ∀ β → rot {₁₊ k} β ↑ ≈ Ypl true β • Ypl false β
    Y-pl β = trans (sym (halves β)) (cong (Yb-pl β) (Yw-pl β))

    -- The swap of the wires 1 2 around Ex • g • Ex is g placed by k₀.
    pl-k₀ : ∀ (g : Circuit N) → S₁₂.⟪ Ex • g • Ex ⟫ ≈ pl k₀ g
    pl-k₀ g = by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl

    S₁₂-X : S₁₂.⟪ X ⟫ ≈ X
    S₁₂-X = fixc (sym (X-↑ Ex)) Ex↑²

    -- X on wire 0 around a colouring black there.
    colX0 : ∀ (s : Bits (₄₊ k)) w → col (true ∷ s) (X • w • X) ≈ col (false ∷ s) w
    colX0 s w = sym (trans (front _ (X-↑ (negsB s)))
                           (by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl))

    -- V, and its inverse, coloured on the wires 3 …, as two placed
    -- rotations.
    V-form : ∀ β (c : Bits (₂₊ k)) →
             col (true ∷ true ∷ true ∷ c) (S₁₂.⟪ rot {₁₊ k} β ↑ ⟫) ≈ Vpl true c β • Vpl false c β
    V-form β c = begin
      col c′ (S₁₂.⟪ rot β ↑ ⟫)
        ≈⟨ col-cong′ (trans (S₁₂.⟪⟫-cong (sym (halves β))) (S₁₂.⟪⟫-• _ _)) ⟩
      col c′ (S₁₂.⟪ S₀.⟪ rot β ⟫ ⟫ • S₁₂.⟪ X • S₀.⟪ rot β ⟫ • X ⟫)
        ≈⟨ col-• c′ _ _ ⟩
      col c′ (S₁₂.⟪ S₀.⟪ rot β ⟫ ⟫) • col c′ (S₁₂.⟪ X • S₀.⟪ rot β ⟫ • X ⟫)
        ≈⟨ cong (col-cong′ (pl-k₀ (rot β)))
                (trans (col-cong′ (S₁₂.⟪⟫-•₃ S₁₂-X (pl-k₀ (rot β)) S₁₂-X)) (colX0 (true ∷ true ∷ c) (pl k₀ (rot β)))) ⟩
      Vpl true c β • Vpl false c β ∎
      where
      c′ : Bits N
      c′ = true ∷ true ∷ true ∷ c
      col-cong′ : ∀ {a b : Circuit N} → a ≈ b → col c′ a ≈ col c′ b
      col-cong′ e = mid _ _ e

    -- Four pairs commute, so the products do.
    four : ∀ {a b c d : Circuit N} → a • c ≈ c • a → a • d ≈ d • a → b • c ≈ c • b → b • d ≈ d • b →
           (a • b) • (c • d) ≈ (c • d) • (a • b)
    four ac ad bc bd = passL (pass₂ ac ad) (pass₂ bc bd)

    yV : ∀ β (c : Bits (₂₊ k)) → c ≢ replicate (₂₊ k) true →
         Y • col (true ∷ true ∷ true ∷ c) (S₁₂.⟪ rot {₁₊ k} β ↑ ⟫) ≈ col (true ∷ true ∷ true ∷ c) (S₁₂.⟪ rot {₁₊ k} β ↑ ⟫) • Y
    yV β c ne = both (sym (Y-pl false)) (sym (V-form β c))
                     (four (yv true true false β c ne) (yv true false false β c ne)
                           (yv false true false β c ne) (yv false false false β c ne))

    ------------------------------------------------------------------
    -- Every colouring of R but the black one passes Y

    Rc : Bits (₂₊ k) → Circuit N
    Rc c = col (true ∷ true ∷ true ∷ c) R

    sepR : ∀ c → c ≢ replicate (₂₊ k) true → Y • Rc c ≈ Rc c • Y
    sepR c ne = both refl (sym form) (pass₂ YC (pass₂ (yV false c ne) (pass₂ YC (yV true c ne))))
      where
      c′ : Bits N
      c′ = true ∷ true ∷ true ∷ c
      YC : Y • CH₂ ≈ CH₂ • Y
      YC = sym N2′
      form : Rc c ≈ CH₂ • col c′ V • CH₂ • col c′ Vi
      form = begin
        col c′ R
          ≈⟨ mid _ _ R-form ⟩
        col c′ (CH₂ • V • CH₂ • Vi)
          ≈⟨ trans (col-• c′ _ _) (back _ (trans (col-• c′ _ _) (back _ (col-• c′ _ _)))) ⟩
        col c′ CH₂ • col c′ V • col c′ CH₂ • col c′ Vi
          ≈⟨ cong (colCH₂ c) (back _ (front _ (colCH₂ c))) ⟩
        CH₂ • col c′ V • CH₂ • col c′ Vi ∎

    ------------------------------------------------------------------
    -- The D-trick: Y passes R • CH

    CH-∏ : CH ↓ ≈ ∏ (allBits (₂₊ k)) Rc
    CH-∏ = begin
      CH ↓
        ≈⟨ sym (S₁₂.⟪⟫-⟪⟫ CH) ⟩
      S₁₂.⟪ CH₂ ⟫
        ≈⟨ S₁₂.⟪⟫-cong (CH₂-∏′ k below) ⟩
      S₁₂.⟪ ∏ (allBits (₂₊ k)) (Hcol k below) ⟫
        ≈⟨ ∏-conj (Ex ↑) Ex↑² (allBits (₂₊ k)) (Hcol k below) ⟩
      ∏ (allBits (₂₊ k)) (λ y → S₁₂.⟪ Hcol k below y ⟫)
        ≈⟨ ∏-cong (allBits (₂₊ k)) (λ y → conj-swap (lemma-cong↑ _ _ (low-comm Ex (negsB y))) HG) ⟩
      ∏ (allBits (₂₊ k)) Rc ∎

    R-CH : R • CH ↓ ≈ CH ↓ • R
    R-CH = S₁₂.⟪⟫-≈ (HG-CH₂ k below) (S₁₂.⟪⟫-•₂ refl (S₁₂.⟪⟫-⟪⟫ CH)) (S₁₂.⟪⟫-•₂ (S₁₂.⟪⟫-⟪⟫ CH) refl)

    Rc1 : Rc (replicate (₂₊ k) true) ≈ R
    Rc1 = trans (≡→≈ (Eq.cong (λ z → z • R • z) (allT N))) (trans left-unit right-unit)

    Y-D : Y • (R • CH ↓) ≈ (R • CH ↓) • Y
    Y-D = both refl (trans (front _ (sym CH-∏)) (sym R-CH))
               (pass-last′ (₂₊ k) Rc sepR (trans (front _ Rc1) R²))

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

    rc : (Y • R • Yi) • (Y • CH ↓ • Yi) ≈ R • CH ↓
    rc = begin
      (Y • R • Yi) • (Y • CH ↓ • Yi)
        ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
      Y • R • (Yi • Y) • CH ↓ • Yi
        ≈⟨ back _ (back _ (trans (front _ Yi-Y) left-unit)) ⟩
      Y • R • CH ↓ • Yi
        ≈⟨ by-passoc (□ • □ • □ • □) ((□ • (□ • □)) • □) Eq.refl ⟩
      (Y • (R • CH ↓)) • Yi
        ≈⟨ front _ Y-D ⟩
      ((R • CH ↓) • Y) • Yi
        ≈⟨ trans assoc (trans (back _ Y-Yi) right-unit) ⟩
      R • CH ↓ ∎

  ----------------------------------------------------------------------
  -- L1, and (43) at the canonical position

  L1 : Y • R • Yi ≈ R • HG
  L1 = begin
    Y • R • Yi
      ≈⟨ sym (trans (back _ sq) right-unit) ⟩
    (Y • R • Yi) • ((Y • CH ↓ • Yi) • (Y • CH ↓ • Yi))
      ≈⟨ trans (sym assoc) (front _ rc) ⟩
    (R • CH ↓) • (Y • CH ↓ • Yi)
      ≈⟨ back _ hgform ⟩
    (R • CH ↓) • (CH ↓ • HG)
      ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
    R • (CH ↓ • CH ↓) • HG
      ≈⟨ back _ (trans (front _ CH²) left-unit) ⟩
    R • HG ∎

  private
    S₁₂X₁ : S₁₂.⟪ X ↑ ⟫ ≈ X ↑ ↑
    S₁₂X₁ = X-step 1 (s≤s (s≤s z≤n))

    X₂-R : X ↑ ↑ • R ≈ R • X ↑ ↑
    X₂-R = C₁₂.carry S₁₂X₁ refl X-Hg

    Cr-R : X ↑ ↑ • (Ex ↑ • Ex ↓) • ΛH (₃₊ k) • (Ex ↓ • Ex ↑) • X ↑ ↑ ≈ R
    Cr-R = begin
      X ↑ ↑ • (Ex ↑ • Ex ↓) • ΛH (₃₊ k) • (Ex ↓ • Ex ↑) • X ↑ ↑
        ≈⟨ by-passoc (□ • (□ • □) • □ • (□ • □) • □) (□ • (□ • (□ • □ • □) • □) • □) Eq.refl ⟩
      X ↑ ↑ • (Ex ↑ • (Ex ↓ • ΛH (₃₊ k) • Ex ↓) • Ex ↑) • X ↑ ↑
        ≈⟨ mid _ _ (mid _ _ S-ΛH) ⟩
      X ↑ ↑ • R • X ↑ ↑
        ≈⟨ fixc X₂-R X↑↑² ⟩
      R ∎

    Λ-R : Λ • R ≈ R • Λ
    Λ-R = C₁₂.carry (fixc (symAt 0) Ex↑²) refl eq338xy

    Λ-RH : Λ • (R • HG) ≈ (R • HG) • Λ
    Λ-RH = pass₂ Λ-R eq338xy

  core43 : (X ↑ ↑ • (Ex ↑ • Ex ↓) • ΛH (₃₊ k) • (Ex ↓ • Ex ↑) • X ↑ ↑) • (Ex ↓ • ΛH (₃₊ k) • Ex ↓)
         ≈ Cc {₂₊ k} • (X ↑ ↑ • (Ex ↑ • Ex ↓) • ΛH (₃₊ k) • (Ex ↓ • Ex ↑) • X ↑ ↑) • Cc {₂₊ k}
  core43 = begin
    Cr • (Ex ↓ • ΛH (₃₊ k) • Ex ↓)
      ≈⟨ cong Cr-R S-ΛH ⟩
    R • HG
      ≈⟨ sym (trans (back _ Λ²) right-unit) ⟩
    (R • HG) • (Λ • Λ)
      ≈⟨ trans (sym assoc) (front _ (sym Λ-RH)) ⟩
    (Λ • (R • HG)) • Λ
      ≈⟨ front _ (back _ (sym L1)) ⟩
    (Λ • (Y • R • Yi)) • Λ
      ≈⟨ by-passoc ((□ • (□ • □ • □)) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
    (Λ • Y) • R • (Yi • Λ)
      ≈⟨ sym (cong (eq361 k below) (cong Cr-R eq361′)) ⟩
    Cc • Cr • Cc ∎
    where
    Cr : Circuit N
    Cr = X ↑ ↑ • (Ex ↑ • Ex ↓) • ΛH (₃₊ k) • (Ex ↓ • Ex ↑) • X ↑ ↑
