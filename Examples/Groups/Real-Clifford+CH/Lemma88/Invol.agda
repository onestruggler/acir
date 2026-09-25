------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.8 on (29) and (41): the decoded letters that are involutions
-- (Clément, Appendix E.5)
--
-- (29), (−1)_[a] X_[a,a+1] (−1)_[a+1] X_[a,a+1] = ε, decodes to the
-- multi-controlled ZX and XZ of one layout, which are inverse: the ZX is
-- CH E CH E and the XZ E CH E CH, E the box under the swap, and the box
-- is an involution (the paper's (317), from (299)).  (41), the square of
-- H_[0,1] H_[3,2], decodes to the square of the multi-controlled H, the
-- box between two P ⊗ P (the paper's (312)).  A gate placed by a layout
-- is conjugated by its negations and its shift, so products of gates
-- with the same layout are the gate of the product (`conj₁-•`,
-- `conj₂-•`).
--
-- Parameters: the canonical box facts at the width, and completeness on
-- two qubits (for P ⊗ P, through ThreeQubit).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon)

module Examples.Groups.Real-Clifford+CH.Lemma88.Invol
  {m : ℕ} (C : Canon m)
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false)
open import Data.Fin using (Fin ; toℕ)
open import Data.Nat using (zero ; suc ; _^_)
open import Data.Nat.Properties using (n<1+n ; <⇒≢)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; X² ; CH² ; Ex²)
open import Examples.Groups.Real-Clifford+CH.Reverse using (rev ; rev-cong)
open import Examples.Groups.Real-Clifford+CH.MultiControlled
  using (Slot ; ctrl ; tgt ; tgtH ; Layout ; negs ; tgtWire ; hWire ; conj₁ ; conj₂ ;
         shiftDown ; shiftUp ; shiftDown₁ ; shiftUp₁ ; mcZX ; mcXZ ; mc±ZX ; mc±XZ ; mcH ; ΛH)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8 using (Succ)
open import Examples.Groups.Real-Clifford+CH.Encoding using (zx ; hhℕ)
open import Examples.Groups.Real-Clifford+CH.Decoding using (d ; dZX ; dZXlo₁ ; dZXhi₁ ; βof ; layout□ ; gadget ; layoutH ; gcode)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂ using (module PP↓ ; PP-CZ↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SwapCalc using (sd-su ; su-sd)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Easy m using (d-zx ; dZX-lo₁ ; dZX-hi₁ ; d-hh0132)

private
  N : ℕ
  N = ₃₊ m

  I : Set
  I = Fin (2 ^ N)

  variable
    k : ℕ

------------------------------------------------------------------------
-- Gates placed by one layout

private
  negs² : ∀ (L : Layout k) → k ⊢ negs L • negs L ≈ ε
  negs² {k} [] = left-unit
    where open Tools (k VRel,_===_)
  negs² {suc k} (ctrl false ∷ L) = begin
    (X • negs L ↑) • (X • negs L ↑)     ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
    X • (negs L ↑ • X) • negs L ↑       ≈⟨ back _ (front _ (sym (X-↑ (negs L)))) ⟩
    X • (X • negs L ↑) • negs L ↑       ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • (□ • □)) Eq.refl ⟩
    (X • X) • (negs L ↑ • negs L ↑)     ≈⟨ trans (front _ X²) left-unit ⟩
    negs L ↑ • negs L ↑                 ≈⟨ lemma-cong↑ (negs L • negs L) ε (negs² L) ⟩
    ε ∎
    where open Tools ((₁₊ k) VRel,_===_)
  negs² {suc k} (ctrl true ∷ L) = lemma-cong↑ (negs L • negs L) ε (negs² L)
  negs² {suc k} (tgt ∷ L)       = lemma-cong↑ (negs L • negs L) ε (negs² L)
  negs² {suc k} (tgtH ∷ L)      = lemma-cong↑ (negs L • negs L) ε (negs² L)

open Tools (N VRel,_===_)

private
  ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
  ≡→≈ Eq.refl = refl

  -- A gate between n s and u n, n an involution and u the inverse of s:
  -- gates g, g′ with g g′ ≈ ε placed so multiply to ε.
  sandwich-inv : ∀ (n s u : Circuit N) → n • n ≈ ε → u • s ≈ ε → s • u ≈ ε →
                 ∀ {g g′ : Circuit N} → g • g′ ≈ ε → (n • s • g • u • n) • (n • s • g′ • u • n) ≈ ε
  sandwich-inv n s u nn us su {g} {g′} e = begin
    (n • s • g • u • n) • (n • s • g′ • u • n)
      ≈⟨ by-passoc ((□ • □ • □ • □ • □) • (□ • □ • □ • □ • □)) (□ • □ • □ • ((□ • (□ • □) • □) • □ • □ • □)) Eq.refl ⟩
    n • s • g • ((u • (n • n) • s) • g′ • u • n)
      ≈⟨ back _ (back _ (back _ (front _ (trans (back _ (trans (front _ nn) left-unit)) us)))) ⟩
    n • s • g • (ε • g′ • u • n)
      ≈⟨ back _ (back _ (back _ left-unit)) ⟩
    n • s • g • g′ • u • n
      ≈⟨ back _ (back _ (trans (sym assoc) (trans (front _ e) left-unit))) ⟩
    n • s • u • n
      ≈⟨ back _ (trans (sym assoc) (trans (front _ su) left-unit)) ⟩
    n • n
      ≈⟨ nn ⟩
    ε ∎

  conj₁-inv : ∀ (L : Layout N) {g g′ : Circuit N} → g • g′ ≈ ε → conj₁ L g • conj₁ L g′ ≈ ε
  conj₁-inv L = sandwich-inv (negs L) (shiftDown (tgtWire L)) (shiftUp (tgtWire L))
                             (negs² L) (su-sd (tgtWire L)) (sd-su (tgtWire L))

  sd₁-su₁ : ∀ h → shiftDown₁ {N} h • shiftUp₁ h ≈ ε
  sd₁-su₁ zero    = left-unit
  sd₁-su₁ (suc h) = lemma-cong↑ (shiftDown h • shiftUp h) ε (sd-su h)

  su₁-sd₁ : ∀ h → shiftUp₁ {N} h • shiftDown₁ h ≈ ε
  su₁-sd₁ zero    = left-unit
  su₁-sd₁ (suc h) = lemma-cong↑ (shiftUp h • shiftDown h) ε (su-sd h)

  conj₂-inv : ∀ (L : Layout N) {g g′ : Circuit N} → g • g′ ≈ ε → conj₂ L g • conj₂ L g′ ≈ ε
  conj₂-inv L {g} {g′} e =
    trans (cong (form g) (form g′)) (sandwich-inv (negs L) (S • S₁) (U₁ • U) (negs² L) US SU e)
    where
    t h : ℕ
    t = tgtWire L
    h = hWire L
    S U S₁ U₁ : Circuit N
    S  = shiftDown t
    U  = shiftUp t
    S₁ = shiftDown₁ h
    U₁ = shiftUp₁ h
    form : ∀ w → conj₂ L w ≈ negs L • (S • S₁) • w • (U₁ • U) • negs L
    form w = by-passoc (□ • □ • □ • □ • □ • □ • □) (□ • (□ • □) • □ • (□ • □) • □) Eq.refl
    US : (U₁ • U) • (S • S₁) ≈ ε
    US = begin
      (U₁ • U) • (S • S₁)     ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
      U₁ • (U • S) • S₁       ≈⟨ back _ (trans (front _ (su-sd t)) left-unit) ⟩
      U₁ • S₁                 ≈⟨ su₁-sd₁ h ⟩
      ε ∎
    SU : (S • S₁) • (U₁ • U) ≈ ε
    SU = begin
      (S • S₁) • (U₁ • U)     ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
      S • (S₁ • U₁) • U       ≈⟨ back _ (trans (front _ (sd₁-su₁ h)) left-unit) ⟩
      S • U                   ≈⟨ sd-su t ⟩
      ε ∎

------------------------------------------------------------------------
-- The gates

private
  Λ E : Circuit N
  Λ = Λ□ (₂₊ m)
  E = Ex-conj Λ

  -- The box under the swap is still an involution.
  E² : E • E ≈ ε
  E² = begin
    (Ex • Λ • Ex) • (Ex • Λ • Ex)   ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
    Ex • Λ • (Ex • Ex) • Λ • Ex     ≈⟨ back _ (back _ (trans (front _ Ex²) left-unit)) ⟩
    Ex • Λ • Λ • Ex                 ≈⟨ back _ (trans (sym assoc) (trans (front _ (Canon.invol C)) left-unit)) ⟩
    Ex • Ex                         ≈⟨ Ex² ⟩
    ε ∎

  -- (317): the multi-controlled ZX and XZ are inverse.
  zx-xz : ΛZX (₂₊ m) • ΛXZ (₂₊ m) ≈ ε
  zx-xz = begin
    (CH • E • CH • E) • (E • CH • E • CH)
      ≈⟨ by-passoc ((□ • □ • □ • □) • (□ • □ • □ • □)) (□ • □ • □ • (□ • □) • □ • □ • □) Eq.refl ⟩
    CH • E • CH • (E • E) • CH • E • CH
      ≈⟨ back _ (back _ (back _ (trans (front _ E²) left-unit))) ⟩
    CH • E • CH • CH • E • CH
      ≈⟨ back _ (back _ (trans (sym assoc) (trans (front _ CH²) left-unit))) ⟩
    CH • E • E • CH
      ≈⟨ back _ (trans (sym assoc) (trans (front _ E²) left-unit)) ⟩
    CH • CH
      ≈⟨ CH² ⟩
    ε ∎

  xz-zx : ΛXZ (₂₊ m) • ΛZX (₂₊ m) ≈ ε
  xz-zx = begin
    (E • CH • E • CH) • (CH • E • CH • E)
      ≈⟨ by-passoc ((□ • □ • □ • □) • (□ • □ • □ • □)) (□ • □ • □ • (□ • □) • □ • □ • □) Eq.refl ⟩
    E • CH • E • (CH • CH) • E • CH • E
      ≈⟨ back _ (back _ (back _ (trans (front _ CH²) left-unit))) ⟩
    E • CH • E • E • CH • E
      ≈⟨ back _ (back _ (trans (sym assoc) (trans (front _ E²) left-unit))) ⟩
    E • CH • CH • E
      ≈⟨ back _ (trans (sym assoc) (trans (front _ CH²) left-unit)) ⟩
    E • E
      ≈⟨ E² ⟩
    ε ∎

  pair-β : ∀ β (L : Layout N) → mc±ZX β L • mc±XZ β L ≈ ε
  pair-β false L = conj₁-inv L zx-xz
  pair-β true  L = conj₁-inv L xz-zx

  -- (312): the multi-controlled H is the box between two P ⊗ P.
  ΛH-PP′ : ∀ k → (₃₊ k) ⊢ ΛH (₁₊ k) ≈ PP ↓ • Λ□ (₂₊ k) • PP ↓
  ΛH-PP′ zero    = PB-sym PP-CZ↑
    where open Tools (3 VRel,_===_) renaming (sym to PB-sym)
  ΛH-PP′ (suc k) = PB-refl
    where open Tools ((₄₊ k) VRel,_===_) renaming (refl to PB-refl)

  PP² : PP ↓ • PP ↓ ≈ ε
  PP² = trans (back _ (sym left-unit)) PP↓.⟪⟫-ε

  ΛH² : ΛH (₁₊ m) • ΛH (₁₊ m) ≈ ε
  ΛH² = begin
    ΛH (₁₊ m) • ΛH (₁₊ m)
      ≈⟨ cong (ΛH-PP′ m) (ΛH-PP′ m) ⟩
    (PP ↓ • Λ • PP ↓) • (PP ↓ • Λ • PP ↓)
      ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
    PP ↓ • Λ • (PP ↓ • PP ↓) • Λ • PP ↓
      ≈⟨ back _ (back _ (trans (front _ PP²) left-unit)) ⟩
    PP ↓ • Λ • Λ • PP ↓
      ≈⟨ back _ (trans (sym assoc) (trans (front _ (Canon.invol C)) left-unit)) ⟩
    PP ↓ • PP ↓
      ≈⟨ PP² ⟩
    ε ∎

------------------------------------------------------------------------
-- The rules

-- (29)
e29 : ∀ (a a′ : I) → Succ a a′ → (d ʷ) (zx {N} a a a′ • zx a′ a a′) ≈ ε
e29 a a′ s = begin
  (d ʷ) (zx a a a′ • zx a′ a a′)
    ≈⟨ ≡→≈ (Eq.trans (Eq.cong₂ _•_ (d-zx a a a′ aa′) (d-zx a′ a a′ aa′))
                     (Eq.cong (λ t → rev (dZX {m} x x t) • rev (dZX t x t)) s)) ⟩
  rev (dZX x x (suc x)) • rev (dZX (suc x) x (suc x))
    ≈⟨ ≡→≈ (Eq.cong₂ (λ u v → rev u • rev v) (dZX-lo₁ x) (dZX-hi₁ x)) ⟩
  rev (dZXhi₁ x • dZXlo₁ x)
    ≈⟨ rev-cong (pair-β (βof x) (layout□ x)) ⟩
  ε ∎
  where
  x : ℕ
  x = toℕ a
  aa′ : a ≢ a′
  aa′ e = <⇒≢ (n<1+n x) (Eq.trans (Eq.cong toℕ e) s)

-- (41)
e41 : (d ʷ) (hhℕ {N} 0 1 3 2 • hhℕ 0 1 3 2) ≈ ε
e41 = begin
  (d ʷ) (hhℕ 0 1 3 2 • hhℕ 0 1 3 2)
    ≈⟨ ≡→≈ (Eq.cong₂ _•_ d-hh0132 d-hh0132) ⟩
  rev (gadget • gadget)
    ≈⟨ rev-cong (conj₂-inv (layoutH {m} (gcode 0) 0 1) ΛH²) ⟩
  ε ∎
