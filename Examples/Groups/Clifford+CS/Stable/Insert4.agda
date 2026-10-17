------------------------------------------------------------------------
-- Presentations of groups
--
-- The controlled functor and an idle wire inserted as wire 4
--
-- The controlled CS of the wires 0 1 borrows the wires 2 3 (Lambda), so
-- its image one width up is its image one width down with wire 4
-- inserted (`Σᵗ-place`): stretching inserts the idle wire just under
-- the control, and `place 4` (Place) inserts it as wire 4; on six wires
-- they agree by the swap networks alone (`stretch-place₄₀`: TopWeakening's
-- cycle σ and Place's cycle are the same word), and from there a
-- placement at wire 4 passes stretching (`stretch-place₄`).  The gates on
-- the top wire of a domain — the scalar shifted all the way up, S or K
-- there, the CS on the top two wires (`topS`, `top1`, `top2`) — have
-- their images in closed form (`λ¹-topS`, `λ¹-top1`, `λ¹-top2`), shifted
-- far enough up from six or nine wires on to leave the wires 0 … 3 alone
-- (`place₄-↑`).  So a commutation of the CS on the wires 0 1 with a gate
-- reaching the top wire goes down a width under λ¹ (Stable.Transport).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Stable.Insert4 where

open import Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.MultiControlled using (top ; CK₁₀)
open import Examples.Groups.Clifford+CS.Swaps using (Swap²)
open import Examples.Groups.Clifford+CS.TopWeakening using (top-cong ; σ ; σ⁻¹ ; σσ⁻¹ ; nat)
open import Examples.Groups.Clifford+CS.Place
  using (place ; cyc ; cyc⁻¹ ; cyc-cyc⁻¹ ; cyc⁻¹-cyc ; cyc-high ; place-high ; ↑ᵏ-↑)
open import Examples.Groups.Clifford+CS.Lambda
open import Examples.Groups.Clifford+CS.Lambda.Split using (top-↑)
open import Examples.Groups.Clifford+CS.Five.Letters using (b-Sb0-2-43-1)

private
  variable
    k m n r : ℕ

  ₅₊ ₆₊ ₇₊ : ℕ → ℕ
  ₅₊ n = suc (₄₊ n)
  ₆₊ n = suc (₅₊ n)
  ₇₊ n = suc (₆₊ n)

  refl≡ : ∀ {n} {a b : Circuit n} → a ≡ b → n ⊢ a ≈ b
  refl≡ Eq.refl = PB.refl

------------------------------------------------------------------------
-- Shifting

private
  ↑ᵏ0 : (v : Circuit n) → v ↑ᵏ 0 ≡ v
  ↑ᵏ0 [ g ]ʷ  = Eq.refl
  ↑ᵏ0 ε       = Eq.refl
  ↑ᵏ0 (u • v) = Eq.cong₂ _•_ (↑ᵏ0 u) (↑ᵏ0 v)

  -- Shifting k + 1 wires is shifting k and then one.
  ↑ᵏs : (v : Circuit n) (k : ℕ) → v ↑ᵏ suc k ≡ (v ↑ᵏ k) ↑
  ↑ᵏs v k = Eq.sym (↑ᵏ-↑ v k)

  ↑ᵏ4 : (v : Circuit n) → v ↑ᵏ 4 ≡ v ↑ ↑ ↑ ↑
  ↑ᵏ4 v = Eq.trans (↑ᵏs v 3) (Eq.cong _↑ (Eq.trans (↑ᵏs v 2) (Eq.cong _↑ (Eq.trans (↑ᵏs v 1)
            (Eq.cong _↑ (Eq.trans (↑ᵏs v 0) (Eq.cong _↑ (↑ᵏ0 v))))))))

  ↑ᵏ5 : (v : Circuit n) → v ↑ᵏ 5 ≡ v ↑ ↑ ↑ ↑ ↑
  ↑ᵏ5 v = Eq.trans (↑ᵏs v 4) (Eq.cong _↑ (↑ᵏ4 v))

-- A circuit four wires up, with wire 4 inserted, is five wires up.
place₄-↑ : (v : Circuit n) → (₅₊ n) ⊢ place 4 (v ↑ ↑ ↑ ↑) ≈ v ↑ ↑ ↑ ↑ ↑
place₄-↑ v = Eq.subst₂ (λ x y → _ ⊢ place 4 x ≈ y) (↑ᵏ4 v) (↑ᵏ5 v) (place-high 4 v)

------------------------------------------------------------------------
-- Stretching and placing at wire 4 on six wires

private
  -- The cycle σ with an idle wire on top, then σ one wire wider: the
  -- exchange of the top two wires.
  σ-step : ∀ i → (₂₊ i) ⊢ top (σ⁻¹ i) • σ (suc i) ≈ Swᵗ i
  σ-step zero    = PB.trans PB.left-unit PB.right-unit
  σ-step (suc i) = begin
    (top (σ⁻¹ i ↑) • Swap) • (Swap • σ (suc i) ↑)
      ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
    top (σ⁻¹ i ↑) • (Swap • Swap) • σ (suc i) ↑
      ≈⟨ back _ (front _ Swap²) ⟩
    top (σ⁻¹ i ↑) • ε • σ (suc i) ↑
      ≈⟨ back _ left-unit ⟩
    top (σ⁻¹ i ↑) • σ (suc i) ↑
      ≈⟨ refl≡ (Eq.cong (λ x → x • σ (suc i) ↑) (top-↑ (σ⁻¹ i))) ⟩
    top (σ⁻¹ i) ↑ • σ (suc i) ↑
      ≈⟨ lemma-cong↑ (top (σ⁻¹ i) • σ (suc i)) (Swᵗ i) (σ-step i) ⟩
    Swᵗ (suc i) ∎
    where open Tools ((₃₊ i) VRel,_===_)

  σ-step′ : ∀ i → (₂₊ i) ⊢ σ⁻¹ (suc i) • top (σ i) ≈ Swᵗ i
  σ-step′ zero    = PB.trans PB.right-unit PB.left-unit
  σ-step′ (suc i) = begin
    (σ⁻¹ (suc i) ↑ • Swap) • (Swap • top (σ i ↑))
      ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
    σ⁻¹ (suc i) ↑ • (Swap • Swap) • top (σ i ↑)
      ≈⟨ back _ (front _ Swap²) ⟩
    σ⁻¹ (suc i) ↑ • ε • top (σ i ↑)
      ≈⟨ back _ left-unit ⟩
    σ⁻¹ (suc i) ↑ • top (σ i ↑)
      ≈⟨ refl≡ (Eq.cong (λ x → σ⁻¹ (suc i) ↑ • x) (top-↑ (σ i))) ⟩
    σ⁻¹ (suc i) ↑ • top (σ i) ↑
      ≈⟨ lemma-cong↑ (σ⁻¹ (suc i) • top (σ i)) (Swᵗ i) (σ-step′ i) ⟩
    Swᵗ (suc i) ∎
    where open Tools ((₃₊ i) VRel,_===_)

stretch-place₄₀ : (c : Circuit 5) → 6 ⊢ stretch c ≈ place 4 c
stretch-place₄₀ c = sym (begin
  cyc⁻¹ 4 • c ↑ • cyc 4
    ≈⟨ back _ (front _ (sym right-unit)) ⟩
  cyc⁻¹ 4 • (c ↑ • ε) • cyc 4
    ≈⟨ back _ (front _ (back _ (sym (σσ⁻¹ 5)))) ⟩
  cyc⁻¹ 4 • (c ↑ • σ 5 • σ⁻¹ 5) • cyc 4
    ≈⟨ back _ (front _ (trans (sym assoc) (front _ (nat c)))) ⟩
  cyc⁻¹ 4 • ((σ 5 • top c) • σ⁻¹ 5) • cyc 4
    ≈⟨ by-passoc (□ • ((□ • □) • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
  (cyc⁻¹ 4 • σ 5) • top c • (σ⁻¹ 5 • cyc 4)
    ≈⟨ cong (σ-step 4) (back _ (σ-step′ 4)) ⟩
  Swᵗ 4 • top c • Swᵗ 4 ∎)
  where open Tools (6 VRel,_===_)

------------------------------------------------------------------------
-- Stretching passes a placement at wire 4 from seven wires on

private
  top-place₄ : (c : Circuit (₅₊ r)) → top (place 4 c) ≡ place 4 (top c)
  top-place₄ c = Eq.cong (λ x → cyc⁻¹ 4 • x • cyc 4) (top-↑ c)

  -- A circuit five wires up passes the cycle of the wires 0 … 4.
  cyc-pass : (v : Circuit n) → (₅₊ n) ⊢ cyc 4 • v ↑ ↑ ↑ ↑ ↑ ≈ v ↑ ↑ ↑ ↑ ↑ • cyc 4
  cyc-pass v = Eq.subst (λ x → _ ⊢ cyc 4 • x ≈ x • cyc 4) (↑ᵏ5 v) (cyc-high 4 v)

  cyc⁻¹-pass : (v : Circuit n) → (₅₊ n) ⊢ cyc⁻¹ 4 • v ↑ ↑ ↑ ↑ ↑ ≈ v ↑ ↑ ↑ ↑ ↑ • cyc⁻¹ 4
  cyc⁻¹-pass {n} v = begin
    C⁻ • V                     ≈⟨ trans (sym right-unit) (back _ (sym (cyc-cyc⁻¹ 4))) ⟩
    (C⁻ • V) • (C • C⁻)        ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
    C⁻ • (V • C) • C⁻          ≈⟨ back _ (front _ (sym (cyc-pass v))) ⟩
    C⁻ • (C • V) • C⁻          ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • (□ • □)) Eq.refl ⟩
    (C⁻ • C) • (V • C⁻)        ≈⟨ trans (front _ (cyc⁻¹-cyc 4)) left-unit ⟩
    V • C⁻ ∎
    where
    open Tools ((₅₊ n) VRel,_===_)
    C = cyc 4
    C⁻ = cyc⁻¹ 4
    V = v ↑ ↑ ↑ ↑ ↑

stretch-place₄ : (c : Circuit (₅₊ r)) → (₇₊ r) ⊢ stretch (place 4 c) ≈ place 4 (stretch c)
stretch-place₄ {r} c = begin
  T • top (place 4 c) • T
    ≈⟨ refl≡ (Eq.cong (λ x → T • x • T) (top-place₄ c)) ⟩
  T • (C⁻ • top c ↑ • C) • T
    ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
  (T • C⁻) • top c ↑ • (C • T)
    ≈⟨ cong (sym (cyc⁻¹-pass (Swᵗ r))) (back _ (cyc-pass (Swᵗ r))) ⟩
  (C⁻ • T) • top c ↑ • (T • C)
    ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
  C⁻ • (T • top c ↑ • T) • C ∎
  where
  open Tools ((₇₊ r) VRel,_===_)
  T = Swᵗ (₅₊ r)
  C = cyc 4
  C⁻ = cyc⁻¹ 4

-- The controlled CS of the wires 0 1, one width up, is the image one
-- width down with wire 4 inserted.
Σᵗ-place : ∀ m → (₂₊ (₄₊ m)) ⊢ Σᵗ (suc m) ≈ place 4 (Σᵗ m)
Σᵗ-place zero    = stretch-place₄₀ (Σᵗ 0)
Σᵗ-place (suc m) =
  PB.trans (PB.cong PB.refl (PB.cong (top-cong (Σᵗ-place m)) PB.refl)) (stretch-place₄ (Σᵗ m))

------------------------------------------------------------------------
-- The gates on the top wire and their images

-- The scalar shifted all the way up, S or K on the top wire, and the CS
-- on the top two wires.
topS : (k : ℕ) → Gen (suc k)
topS zero    = gate₀ I-gate ↥
topS (suc k) = topS k ↥

top1 : (k : ℕ) → Gate 1 → Gen (suc k)
top1 zero    h = gate₁ h
top1 (suc k) h = top1 k h ↥

top2 : (k : ℕ) → Gate 2 → Gen (₂₊ k)
top2 zero    h = gate₂ h
top2 (suc k) h = top2 k h ↥

λ¹-topS : ∀ m → λ¹ {m} (topS (₃₊ m)) ≡ Sᵗ (₄₊ m)
λ¹-topS zero    = Eq.refl
λ¹-topS (suc m) = Eq.cong _↑ (λ¹-topS m)

-- S or K between wire 0 and the control, shifted.
Zᵗ : (m : ℕ) → Gate 1 → Circuit (₂₊ m)
Zᵗ zero    S-gate = CSᵗ ₀
Zᵗ zero    K-gate = CKᵗ ₀
Zᵗ (suc m) h      = Zᵗ m h ↑

λ¹-top1 : ∀ m h → λ¹ {m} (top1 (₃₊ m) h) ≡ Zᵗ m h ↑ ↑ ↑
λ¹-top1 zero    S-gate = Eq.refl
λ¹-top1 zero    K-gate = Eq.refl
λ¹-top1 (suc m) h      = Eq.cong _↑ (λ¹-top1 m h)

-- The four-wire domain's CS on its top two wires, shifted.
W : (m : ℕ) → Circuit (₅₊ m)
W zero    = b-Sb0-2-43-1
W (suc m) = W m ↑

λ¹-top2 : ∀ m → λ¹ {m} (top2 (₂₊ m) CS-gate) ≡ W m
λ¹-top2 zero    = Eq.refl
λ¹-top2 (suc m) = Eq.cong _↑ (λ¹-top2 m)
