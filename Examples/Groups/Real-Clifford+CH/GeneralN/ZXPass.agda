------------------------------------------------------------------------
-- Presentations of groups
--
-- The CH and CZ from an idle wire pass the multi-controlled ZX, and the
-- CH passes the box (Clément, Lemma D.8, Equations (278)–(280))
--
-- (278) is the paper's proof, step by step (checked diagram by diagram
-- numerically first, scratchpad t278.py).  On the wires 0 1 the pair
-- HC • CZ is a rotation of wire 1 controlled by wire 0, and the ZX on
-- wire 1 is a rotation controlled by the wires 2 …; the proof splits the
-- ZX as CH • B • CH • B, moves the pair past the pieces on three wires,
-- and turns what is left, by four steps one width down with wire 0 idle
-- (GeneralN.SemZX), into the H gate and the box with their box wire on
-- wire 2 — which by (274) and (276) can be moved to wire 0, where the
-- pair passes them by a step one width down with wire 2 idle.
--
-- (279) is (278) twice around the box as the square of the ZX, (355)
-- one width down; (280) is (279) and the CZ from wire 0 onto the box
-- wire, (272).
--
-- The width is 4 + k and every step one width down uses completeness
-- at 3 + k, which at k = 0 is completeness on three qubits.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.ZXPass
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ ; zero ; suc)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; Ex² ; ax)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃ using (L₃-sem)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box complete₂ complete₃ using (eq272)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxWire complete₂ complete₃ using (eq274)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PPBox complete₂ complete₃ using (eq276)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Sem using (sem285)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SemZX
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place
  using (place ; place-• ; place-low ; lemma-5-1 ; low-comm)

-- Completeness at 3 + k.
Complete : ℕ → Set
Complete k = ∀ {u v : Circuit (₃₊ k)} → ⟦ u ⟧ ~ ⟦ v ⟧ → (₃₊ k) ⊢ u ≈ v

private
  -- A gate that passes w and is its own inverse passes around it.
  unconj : ∀ {m} {a w : Circuit m} → m ⊢ a • w ≈ w • a → m ⊢ a • a ≈ ε → m ⊢ a • w • a ≈ w
  unconj {m} {a} {w} c e = begin
    a • w • a       ≈⟨ sym assoc ⟩
    (a • w) • a     ≈⟨ front _ c ⟩
    (w • a) • a     ≈⟨ cancelʳ _ e ⟩
    w ∎
    where open Tools (m VRel,_===_)

------------------------------------------------------------------------
-- The box one wire up, (272), (274) and (276) at width 4 + k: with two
-- controls it is a CZ two wires up, which passes anything on the wires
-- 0 1; with more they are GeneralN's, one width down.

box272 : ∀ k → (₄₊ k) ⊢ CZ ↓ • Λ□ (₂₊ k) ↑ ≈ Λ□ (₂₊ k) ↑ • CZ ↓
box272 zero    = low-comm CZ CZ
box272 (suc k) = eq272 k

box274 : ∀ k → Complete k → (₄₊ k) ⊢ Ex ↓ • Λ□ (₂₊ k) ↑ • Ex ↓ ≈ Λ□ (₂₊ k) ↑
box274 zero    c = unconj (low-comm Ex CZ) Ex²
box274 (suc k) c = eq274 k (c (sem285 k))

box276 : ∀ k → Complete k → (₄₊ k) ⊢ PP ↓ • Λ□ (₂₊ k) ↑ • PP ↓ ≈ Λ□ (₂₊ k) ↑
box276 zero    c = unconj (low-comm PP CZ) (L₃-sem (PP • PP) ε Eq.refl)
box276 (suc k) c = eq276 k c

------------------------------------------------------------------------
-- (278)

Eq278 Eq279 Eq280 : ℕ → Set
Eq278 k = (₄₊ k) ⊢ HC • CZ • ΛZX (₂₊ k) ↑ ≈ ΛZX (₂₊ k) ↑ • HC • CZ
Eq279 k = (₄₊ k) ⊢ HC • CZ • Λ□ (₂₊ k) ↑ ≈ Λ□ (₂₊ k) ↑ • HC • CZ
Eq280 k = (₄₊ k) ⊢ HC • Λ□ (₂₊ k) ↑ ≈ Λ□ (₂₊ k) ↑ • HC

module _ (k : ℕ) (complete : Complete k) where

  private
    open Tools ((₄₊ k) VRel,_===_)

    -- A step one width down, one wire up.
    up : ∀ {u v : Circuit (₃₊ k)} → ⟦ u ⟧ ~ ⟦ v ⟧ → (₄₊ k) ⊢ u ↑ ≈ v ↑
    up {u} {v} e = lemma-cong↑ u v (complete e)

    -- The gates at width 4 + k.
    Λ↑ B₂₁ HG₁₂ ZX₂ XZ₂ B₀₁ HG₁₀ PP₀₂ : Circuit (₄₊ k)
    Λ↑   = Λ□ (₂₊ k) ↑
    B₂₁  = B₁₀ k ↑                    -- box 2, controls 1, 3 …
    HG₁₂ = HG₀₁ k ↑                   -- H on 1, box 2, controls 3 …
    ZX₂  = ZX₁ k ↑                    -- ZX on 2, controls 3 …
    XZ₂  = XZ₁ k ↑
    B₀₁  = place 2 (Λ□ (₂₊ k))        -- box 0, controls 1, 3 …
    HG₁₀ = PP ↓ • B₀₁ • PP ↓          -- H on 1, box 0, controls 3 …
    PP₀₂ = Ex ↑ • PP ↓ • Ex ↑

    CZ↑² : (₄₊ k) ⊢ CZ ↑ • CZ ↑ ≈ ε
    CZ↑² = lemma-cong↑ (CZ • CZ) ε (ax order-CZ)

    Ex↑² : (₄₊ k) ⊢ Ex ↑ • Ex ↑ ≈ ε
    Ex↑² = lemma-cong↑ (Ex • Ex) ε Ex²

    ------------------------------------------------------------------
    -- Moving the box wire of B₂₁ and HG₁₂ from wire 2 to wire 0

    move-B : (₄₊ k) ⊢ B₂₁ ≈ B₀₁
    move-B = begin
      Ex ↑ • Λ↑ • Ex ↑
        ≈⟨ back _ (front _ (sym (box274 k complete))) ⟩
      Ex ↑ • (Ex ↓ • Λ↑ • Ex ↓) • Ex ↑
        ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (Ex ↑ • Ex ↓) • Λ↑ • (Ex ↓ • Ex ↑)
        ≈⟨ cong (front _ (sym left-unit)) (back _ (back _ (sym right-unit))) ⟩
      ((ε • Ex ↑) • Ex ↓) • Λ↑ • (Ex ↓ • (Ex ↑ • ε)) ∎

    pp-B : (₄₊ k) ⊢ PP₀₂ • B₂₁ • PP₀₂ ≈ B₂₁
    pp-B = begin
      (Ex ↑ • PP ↓ • Ex ↑) • (Ex ↑ • Λ↑ • Ex ↑) • (Ex ↑ • PP ↓ • Ex ↑)
        ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □) • (□ • □ • □))
                     (□ • □ • (□ • □) • □ • (□ • □) • □ • □) Eq.refl ⟩
      Ex ↑ • PP ↓ • (Ex ↑ • Ex ↑) • Λ↑ • (Ex ↑ • Ex ↑) • PP ↓ • Ex ↑
        ≈⟨ back _ (back _ (cong Ex↑² (back _ (front _ Ex↑²)))) ⟩
      Ex ↑ • PP ↓ • ε • Λ↑ • ε • PP ↓ • Ex ↑
        ≈⟨ back _ (back _ (trans left-unit (back _ left-unit))) ⟩
      Ex ↑ • PP ↓ • Λ↑ • PP ↓ • Ex ↑
        ≈⟨ back _ (by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl) ⟩
      Ex ↑ • (PP ↓ • Λ↑ • PP ↓) • Ex ↑
        ≈⟨ back _ (front _ (box276 k complete)) ⟩
      Ex ↑ • Λ↑ • Ex ↑ ∎

    klein₁ : (₄₊ k) ⊢ PP ↑ • PP₀₂ ≈ PP ↓
    klein₁ = L₃-sem (PP ↑ • Ex ↑ • PP ↓ • Ex ↑) PP Eq.refl

    klein₂ : (₄₊ k) ⊢ PP₀₂ • PP ↑ ≈ PP ↓
    klein₂ = L₃-sem ((Ex ↑ • PP ↓ • Ex ↑) • PP ↑) PP Eq.refl

    move-HG : (₄₊ k) ⊢ HG₁₂ ≈ HG₁₀
    move-HG = begin
      PP ↑ • B₂₁ • PP ↑                          ≈⟨ back _ (front _ (sym pp-B)) ⟩
      PP ↑ • (PP₀₂ • B₂₁ • PP₀₂) • PP ↑          ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (PP ↑ • PP₀₂) • B₂₁ • (PP₀₂ • PP ↑)        ≈⟨ cong klein₁ (back _ klein₂) ⟩
      PP ↓ • B₂₁ • PP ↓                          ≈⟨ back _ (front _ move-B) ⟩
      PP ↓ • B₀₁ • PP ↓ ∎

    move-HGB : (₄₊ k) ⊢ HG₁₂ • B₂₁ ≈ HG₁₀ • B₀₁
    move-HGB = cong move-HG move-B

    ------------------------------------------------------------------
    -- The step with wire 2 idle

    place-HG′ : (₄₊ k) ⊢ place 2 (HG′ k) ≈ HG₁₀
    place-HG′ = begin
      place 2 (PP ↓ • Λ□ (₂₊ k) • PP ↓)
        ≈⟨ place-• 2 (PP ↓) (Λ□ (₂₊ k) • PP ↓) ⟩
      place 2 (PP ↓) • place 2 (Λ□ (₂₊ k) • PP ↓)
        ≈⟨ back _ (place-• 2 (Λ□ (₂₊ k)) (PP ↓)) ⟩
      place 2 (PP ↓) • B₀₁ • place 2 (PP ↓)
        ≈⟨ cong (place-low 2 PP) (back _ (place-low 2 PP)) ⟩
      PP ↓ • B₀₁ • PP ↓ ∎

    place-hc : (₄₊ k) ⊢ place 2 (HC • CZ) ≈ HC • CZ
    place-hc = place-low 2 (HC • CZ)

    pass-e : (₄₊ k) ⊢ (HC • CZ) • HG₁₀ • B₀₁ ≈ HG₁₀ • B₀₁ • (HC • CZ)
    pass-e = begin
      (HC • CZ) • HG₁₀ • B₀₁
        ≈⟨ cong (sym place-hc) (cong (sym place-HG′) refl) ⟩
      place 2 (HC • CZ) • place 2 (HG′ k) • place 2 (Λ□ (₂₊ k))
        ≈⟨ back _ (sym (place-• 2 (HG′ k) (Λ□ (₂₊ k)))) ⟩
      place 2 (HC • CZ) • place 2 (HG′ k • Λ□ (₂₊ k))
        ≈⟨ sym (place-• 2 (HC • CZ) (HG′ k • Λ□ (₂₊ k))) ⟩
      place 2 ((HC • CZ) • HG′ k • Λ□ (₂₊ k))
        ≈⟨ lemma-5-1 2 complete (sem-e k) ⟩
      place 2 (HG′ k • Λ□ (₂₊ k) • (HC • CZ))
        ≈⟨ place-• 2 (HG′ k) (Λ□ (₂₊ k) • (HC • CZ)) ⟩
      place 2 (HG′ k) • place 2 (Λ□ (₂₊ k) • (HC • CZ))
        ≈⟨ back _ (place-• 2 (Λ□ (₂₊ k)) (HC • CZ)) ⟩
      place 2 (HG′ k) • place 2 (Λ□ (₂₊ k)) • place 2 (HC • CZ)
        ≈⟨ cong place-HG′ (back _ place-hc) ⟩
      HG₁₀ • B₀₁ • (HC • CZ) ∎

    ------------------------------------------------------------------
    -- Moving the pair to the right, on three wires or disjointly

    mv-ZX : (₄₊ k) ⊢ (HC • CZ) • ZX₂ ≈ ZX₂ • (HC • CZ)
    mv-ZX = low-comm (HC • CZ) (ΛZX (₁₊ k))

    mv-XZ : (₄₊ k) ⊢ (HC • CZ) • XZ₂ ≈ XZ₂ • (HC • CZ)
    mv-XZ = low-comm (HC • CZ) (ΛXZ (₁₊ k))

    mv-3 : (₄₊ k) ⊢ (HC • CZ) • (CZ ↑ • CH ↑) ≈ (CZ ↑ • CH ↑) • (HC • CZ)
    mv-3 = L₃-sem ((HC • CZ) • (CZ ↑ • CH ↑)) ((CZ ↑ • CH ↑) • (HC • CZ)) Eq.refl

    mv : (₄₊ k) ⊢ (HC • CZ) • ZX₂ • (CZ ↑ • CH ↑) • XZ₂ ≈ ZX₂ • (CZ ↑ • CH ↑) • XZ₂ • (HC • CZ)
    mv = begin
      (HC • CZ) • ZX₂ • (CZ ↑ • CH ↑) • XZ₂       ≈⟨ sym assoc ⟩
      ((HC • CZ) • ZX₂) • (CZ ↑ • CH ↑) • XZ₂     ≈⟨ front _ mv-ZX ⟩
      (ZX₂ • (HC • CZ)) • (CZ ↑ • CH ↑) • XZ₂     ≈⟨ assoc ⟩
      ZX₂ • (HC • CZ) • (CZ ↑ • CH ↑) • XZ₂       ≈⟨ back _ (sym assoc) ⟩
      ZX₂ • ((HC • CZ) • (CZ ↑ • CH ↑)) • XZ₂     ≈⟨ back _ (front _ mv-3) ⟩
      ZX₂ • ((CZ ↑ • CH ↑) • (HC • CZ)) • XZ₂     ≈⟨ back _ assoc ⟩
      ZX₂ • (CZ ↑ • CH ↑) • (HC • CZ) • XZ₂       ≈⟨ back _ (back _ mv-XZ) ⟩
      ZX₂ • (CZ ↑ • CH ↑) • XZ₂ • (HC • CZ) ∎

    swap₃ : (₄₊ k) ⊢ (HC • CZ) • (CH ↑ • CZ ↑) ≈ (CH ↑ • CZ ↑) • (HC • CZ)
    swap₃ = L₃-sem ((HC • CZ) • (CH ↑ • CZ ↑)) ((CH ↑ • CZ ↑) • (HC • CZ)) Eq.refl

  ----------------------------------------------------------------------
  -- (278)

  eq278 : Eq278 k
  eq278 = begin
    HC • CZ • CH ↑ • B₂₁ • CH ↑ • B₂₁
      ≈⟨ by-passoc (□ • □ • □ • □ • □ • □) ((□ • □) • (□ • □) • □ • □) Eq.refl ⟩
    (HC • CZ) • (CH ↑ • B₂₁) • CH ↑ • B₂₁
      ≈⟨ back _ (front _ (back _ (trans (sym left-unit) (front _ (sym CZ↑²))))) ⟩
    (HC • CZ) • (CH ↑ • (CZ ↑ • CZ ↑) • B₂₁) • CH ↑ • B₂₁
      ≈⟨ by-passoc ((□ • □) • (□ • (□ • □) • □) • □ • □) (((□ • □) • (□ • □)) • (□ • □) • □ • □) Eq.refl ⟩
    ((HC • CZ) • (CH ↑ • CZ ↑)) • (CZ ↑ • B₂₁) • CH ↑ • B₂₁
      ≈⟨ cong swap₃ (front _ (up (sem-a k))) ⟩
    ((CH ↑ • CZ ↑) • (HC • CZ)) • (ZX₂ • CZ ↑ • XZ₂) • CH ↑ • B₂₁
      ≈⟨ back _ (back _ (back _ (trans (sym left-unit) (front _ (sym (up (sem-317 k))))))) ⟩
    ((CH ↑ • CZ ↑) • (HC • CZ)) • (ZX₂ • CZ ↑ • XZ₂) • CH ↑ • (ZX₂ • XZ₂) • B₂₁
      ≈⟨ by-passoc (((□ • □) • (□ • □)) • (□ • □ • □) • □ • (□ • □) • □)
                   ((□ • □) • (□ • □) • □ • □ • (□ • □ • □) • □ • □) Eq.refl ⟩
    (CH ↑ • CZ ↑) • (HC • CZ) • ZX₂ • CZ ↑ • (XZ₂ • CH ↑ • ZX₂) • XZ₂ • B₂₁
      ≈⟨ back _ (back _ (back _ (back _ (front _ (up (sem-b k)))))) ⟩
    (CH ↑ • CZ ↑) • (HC • CZ) • ZX₂ • CZ ↑ • (CH ↑ • HG₁₂) • XZ₂ • B₂₁
      ≈⟨ by-passoc ((□ • □) • □ • □ • □ • (□ • □) • □ • □)
                   ((□ • □) • □ • □ • (□ • □) • (□ • □) • □) Eq.refl ⟩
    (CH ↑ • CZ ↑) • (HC • CZ) • ZX₂ • (CZ ↑ • CH ↑) • (HG₁₂ • XZ₂) • B₂₁
      ≈⟨ back _ (back _ (back _ (back _ (front _ (up (sem-c k)))))) ⟩
    (CH ↑ • CZ ↑) • (HC • CZ) • ZX₂ • (CZ ↑ • CH ↑) • (XZ₂ • HG₁₂) • B₂₁
      ≈⟨ back _ (by-passoc (□ • □ • □ • (□ • □) • □) ((□ • □ • □ • □) • □ • □) Eq.refl) ⟩
    (CH ↑ • CZ ↑) • ((HC • CZ) • ZX₂ • (CZ ↑ • CH ↑) • XZ₂) • HG₁₂ • B₂₁
      ≈⟨ back _ (front _ mv) ⟩
    (CH ↑ • CZ ↑) • (ZX₂ • (CZ ↑ • CH ↑) • XZ₂ • (HC • CZ)) • HG₁₂ • B₂₁
      ≈⟨ back _ (by-passoc ((□ • □ • □ • □) • □ • □) (□ • □ • □ • (□ • □ • □)) Eq.refl) ⟩
    (CH ↑ • CZ ↑) • ZX₂ • (CZ ↑ • CH ↑) • XZ₂ • ((HC • CZ) • HG₁₂ • B₂₁)
      ≈⟨ back _ (back _ (back _ (back _ (back _ move-HGB)))) ⟩
    (CH ↑ • CZ ↑) • ZX₂ • (CZ ↑ • CH ↑) • XZ₂ • ((HC • CZ) • HG₁₀ • B₀₁)
      ≈⟨ back _ (back _ (back _ (back _ pass-e))) ⟩
    (CH ↑ • CZ ↑) • ZX₂ • (CZ ↑ • CH ↑) • XZ₂ • (HG₁₀ • B₀₁ • (HC • CZ))
      ≈⟨ back _ (back _ (back _ (back _ (cong (sym move-HG) (front _ (sym move-B)))))) ⟩
    (CH ↑ • CZ ↑) • ZX₂ • (CZ ↑ • CH ↑) • XZ₂ • (HG₁₂ • B₂₁ • (HC • CZ))
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □) • □ • (□ • □ • □))
                   ((□ • □ • □ • □ • □ • □ • □ • □) • □) Eq.refl ⟩
    (CH ↑ • CZ ↑ • ZX₂ • CZ ↑ • CH ↑ • XZ₂ • HG₁₂ • B₂₁) • (HC • CZ)
      ≈⟨ front _ (up (sem-d k)) ⟩
    ΛZX (₂₊ k) ↑ • (HC • CZ) ∎

  ----------------------------------------------------------------------
  -- (279): the pair passes the box, the square of the ZX

  eq279 : Eq279 k
  eq279 = begin
    HC • CZ • Λ↑
      ≈⟨ back _ (back _ (up (sem-355 k))) ⟩
    HC • CZ • (Z↑ • Z↑)
      ≈⟨ by-passoc (□ • □ • (□ • □)) ((□ • □ • □) • □) Eq.refl ⟩
    (HC • CZ • Z↑) • Z↑
      ≈⟨ front _ eq278 ⟩
    (Z↑ • HC • CZ) • Z↑
      ≈⟨ by-passoc ((□ • □ • □) • □) (□ • (□ • □ • □)) Eq.refl ⟩
    Z↑ • (HC • CZ • Z↑)
      ≈⟨ back _ eq278 ⟩
    Z↑ • (Z↑ • HC • CZ)
      ≈⟨ by-passoc (□ • (□ • □ • □)) ((□ • □) • □ • □) Eq.refl ⟩
    (Z↑ • Z↑) • HC • CZ
      ≈⟨ front _ (sym (up (sem-355 k))) ⟩
    Λ↑ • HC • CZ ∎
    where
    Z↑ : Circuit (₄₊ k)
    Z↑ = ΛZX (₂₊ k) ↑

  ----------------------------------------------------------------------
  -- (280): the CH alone passes the box, the CZ doing so by (272)

  eq280 : Eq280 k
  eq280 = begin
    HC • Λ↑                     ≈⟨ back _ (sym (trans (front _ CZ²) left-unit)) ⟩
    HC • (CZ • CZ) • Λ↑         ≈⟨ back _ assoc ⟩
    HC • CZ • (CZ • Λ↑)         ≈⟨ back _ (back _ (box272 k)) ⟩
    HC • CZ • (Λ↑ • CZ)         ≈⟨ by-passoc (□ • □ • (□ • □)) ((□ • □ • □) • □) Eq.refl ⟩
    (HC • CZ • Λ↑) • CZ         ≈⟨ front _ eq279 ⟩
    (Λ↑ • HC • CZ) • CZ         ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • (□ • □)) Eq.refl ⟩
    Λ↑ • HC • (CZ • CZ)         ≈⟨ back _ (back _ CZ²) ⟩
    Λ↑ • HC • ε                 ≈⟨ back _ right-unit ⟩
    Λ↑ • HC ∎
    where
    CZ² : (₄₊ k) ⊢ CZ • CZ ≈ ε
    CZ² = ax order-CZ
