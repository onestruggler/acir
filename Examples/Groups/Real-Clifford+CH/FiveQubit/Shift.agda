------------------------------------------------------------------------
-- Presentations of groups
--
-- A box wire moved onto the fifth wire: the four-wire gates with their
-- box wire on wire 3 pass the swap of the wires 3 4
--
-- (251) and (252) are about gates one wire up, on the wires 1–4 with the
-- box wire on wire 1 and wire 0 idle.  The four-qubit development states
-- its gates on the wires 0–3.  The two frames differ by the cycle c₄
-- that carries wire 0 to wire 4 and every other wire one down — the
-- naturality `nat` of `TopWeakening`, here under further idle wires
-- (`shift`) — followed by the cycle φ of the wires 0–3 that carries the
-- box wire from wire 0 to wire 3.  Along P = c₄ φ the swap of the wires
-- 0 1 becomes the swap of the wires 3 4 (`Ex-P`), a gate F one wire up
-- becomes F under the three lower swaps (`F-P`), and an equation
-- between them is carried by `transport`.
--
-- So the swap of the wires 3 4 passes the box with its box wire on
-- wire 3 (`Ex₃₄-box₃‴`) and the doubly controlled H with its box wire
-- there (`Ex₃₄-ΛH₂′`), hence their images under X and swaps that leave
-- the wires 3 4 alone.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FiveQubit.Shift
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ ; zero ; suc)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

import Presentation.Base as PB

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; Ex² ; X² ; comm-↓↑ ; S-X↑)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.TopWeakening using (top ; σ ; nat ; top-cong)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃
  using (box₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.ControlledH complete₂ complete₃
  using (ΛH₂′ ; °ΛH₂′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Permutations complete₂ complete₃
  using (Ex₁² ; Ex₂² ; far ; braid↑)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates complete₂ complete₃
  using (box₃‴)
open import Examples.Groups.Real-Clifford+CH.FiveQubit.Auxiliary complete₂ complete₃
  using (box₃↑ ; Ex-box₃↑ ; ΛH₂↑ ; eq252)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (module N₂)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The cycles

-- Wire 0 to wire 4, the wires 1–4 one down.
c₄ : Circuit (₁₊ (₄₊ n))
c₄ = Ex ↓ • Ex ↑ • Ex ↑ ↑ • Ex ↑ ↑ ↑

-- Wire 0 to wire 3, the wires 1–3 one down.
φ : Circuit (₄₊ n)
φ = Ex ↓ • Ex ↑ • Ex ↑ ↑

-- The image of F under the three lower swaps: its wire 0 on wire 3.
Φ : Circuit (₄₊ n) → Circuit (₄₊ n)
Φ F = S₂₃.⟪ S₁₂.⟪ S₀₁.⟪ F ⟫ ⟫ ⟫

P : Circuit (₁₊ (₄₊ n))
P = c₄ • φ

Ex₃² : (₁₊ (₄₊ n)) ⊢ Ex ↑ ↑ ↑ • Ex ↑ ↑ ↑ ≈ ε
Ex₃² = lemma-cong↑ (Ex ↑ ↑ • Ex ↑ ↑) ε Ex₂²

module S₃₄ {n : ℕ} = Conj {₁₊ (₄₊ n)} (Ex ↑ ↑ ↑) Ex₃²

------------------------------------------------------------------------
-- Naturality of c₄ under idle wires on top

private
  top-↑ : (w : Circuit n) → top (w ↑) ≡ top w ↑
  top-↑ [ g ]ʷ  = Eq.refl
  top-↑ ε       = Eq.refl
  top-↑ (w • v) = Eq.cong₂ _•_ (top-↑ w) (top-↑ v)

-- A family of four-wire circuits, one at each width, that adding a wire
-- on top carries to the next: a closed word under `↓ᵏ`.
shift : (f : ∀ m → Circuit (₄₊ m)) → (∀ m → top (f m) ≡ f (suc m)) →
        ∀ m → (₁₊ (₄₊ m)) ⊢ f m ↑ • c₄ ≈ c₄ • f (suc m)
shift f e zero = Eq.subst (λ x → 5 ⊢ f 0 ↑ • c₄ ≈ c₄ • x) (e 0) (begin
  f 0 ↑ • c₄          ≈⟨ back _ (sym σ-c₄) ⟩
  f 0 ↑ • σ 4         ≈⟨ nat (f 0) ⟩
  σ 4 • top (f 0)     ≈⟨ front _ σ-c₄ ⟩
  c₄ • top (f 0) ∎)
  where
  open Tools (5 VRel,_===_)
  σ-c₄ : 5 ⊢ σ 4 ≈ c₄
  σ-c₄ = back _ (back _ (back _ right-unit))
shift f e (suc m) =
  Eq.subst₂ (λ x y → (₂₊ (₄₊ m)) ⊢ x • c₄ ≈ c₄ • y)
            (Eq.trans (top-↑ (f m)) (Eq.cong _↑ (e m))) (e (suc m))
            (top-cong (shift f e m))

------------------------------------------------------------------------
-- Words

module _ {X : Set} (Γ : WRel X) where
  open Tools Γ

  lcancel : ∀ {s u v : Word X} → s • s ≈ ε → s • u ≈ s • v → u ≈ v
  lcancel {s} {u} {v} ss e = begin
    u             ≈⟨ sym (cancelˡ _ ss) ⟩
    s • s • u     ≈⟨ back _ e ⟩
    s • s • v     ≈⟨ cancelˡ _ ss ⟩
    v ∎

  -- An equation carried along a word that need not be an involution.
  transport : ∀ {p x x′ y y′ : Word X} →
              (∀ {u v} → p • u ≈ p • v → u ≈ v) →
              x • p ≈ p • x′ → y • p ≈ p • y′ →
              x • y ≈ y • x → x′ • y′ ≈ y′ • x′
  transport {p} {x} {x′} {y} {y′} cancel xp yp xy = cancel (begin
    p • x′ • y′       ≈⟨ sym assoc ⟩
    (p • x′) • y′     ≈⟨ front _ (sym xp) ⟩
    (x • p) • y′      ≈⟨ assoc ⟩
    x • p • y′        ≈⟨ back _ (sym yp) ⟩
    x • y • p         ≈⟨ sym assoc ⟩
    (x • y) • p       ≈⟨ front _ xy ⟩
    (y • x) • p       ≈⟨ assoc ⟩
    y • x • p         ≈⟨ back _ xp ⟩
    y • p • x′        ≈⟨ sym assoc ⟩
    (y • p) • x′      ≈⟨ front _ yp ⟩
    (p • y′) • x′     ≈⟨ assoc ⟩
    p • y′ • x′ ∎)

------------------------------------------------------------------------
-- Along P

private
  -- A gate F at the bottom, pushed through φ.
  F-φ : (F : Circuit (₄₊ n)) → (₄₊ n) ⊢ F • φ ≈ φ • Φ F
  F-φ {n} F = sym (begin
    (Ex ↓ • Ex ↑ • Ex ↑ ↑) • (Ex ↑ ↑ • (Ex ↑ • (Ex ↓ • F • Ex ↓) • Ex ↑) • Ex ↑ ↑)
      ≈⟨ by-passoc ((□ • □ • □) • (□ • (□ • (□ • □ • □) • □) • □))
                   (□ • □ • (□ • □) • □ • □ • □ • □ • □ • □) Eq.refl ⟩
    Ex ↓ • Ex ↑ • (Ex ↑ ↑ • Ex ↑ ↑) • Ex ↑ • Ex ↓ • F • Ex ↓ • Ex ↑ • Ex ↑ ↑
      ≈⟨ back _ (back _ (cancelˢ _ Ex₂²)) ⟩
    Ex ↓ • Ex ↑ • Ex ↑ • Ex ↓ • F • Ex ↓ • Ex ↑ • Ex ↑ ↑
      ≈⟨ back _ (cancelˡ _ Ex₁²) ⟩
    Ex ↓ • Ex ↓ • F • Ex ↓ • Ex ↑ • Ex ↑ ↑
      ≈⟨ cancelˡ _ Ex² ⟩
    F • Ex ↓ • Ex ↑ • Ex ↑ ↑ ∎)
    where open Tools ((₄₊ n) VRel,_===_)

module _ {n : ℕ} where
  private
    Γ = (₁₊ (₄₊ n)) VRel,_===_
  open Tools Γ

  private
    c₄-tail : c₄ ≈ φ • Ex ↑ ↑ ↑
    c₄-tail = by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl

    φ-shift : φ {n} ↑ • c₄ ≈ c₄ • φ
    φ-shift = shift (λ m → φ {m}) (λ m → Eq.refl) n

  -- The swap of the wires 0 1 becomes the swap of the wires 3 4.
  Ex-P : Ex ↓ • P ≈ P • Ex ↑ ↑ ↑
  Ex-P = sym (begin
    (c₄ • φ) • Ex ↑ ↑ ↑       ≈⟨ assoc ⟩
    c₄ • φ • Ex ↑ ↑ ↑         ≈⟨ back _ (sym c₄-tail) ⟩
    c₄ • c₄                   ≈⟨ assoc ⟩
    Ex ↓ • φ {n} ↑ • c₄       ≈⟨ back _ φ-shift ⟩
    Ex ↓ • c₄ • φ             ≈⟨ refl ⟩
    Ex ↓ • P ∎)

  -- A gate one wire up becomes the gate under the three lower swaps.
  F-P : (f : ∀ m → Circuit (₄₊ m)) → (∀ m → top (f m) ≡ f (suc m)) →
        f n ↑ • P ≈ P • Φ (f (suc n))
  F-P f e = begin
    f n ↑ • c₄ • φ                ≈⟨ sym assoc ⟩
    (f n ↑ • c₄) • φ              ≈⟨ front _ (shift f e n) ⟩
    (c₄ • f (suc n)) • φ          ≈⟨ assoc ⟩
    c₄ • f (suc n) • φ            ≈⟨ back _ (F-φ (f (suc n))) ⟩
    c₄ • φ • Φ (f (suc n))        ≈⟨ sym assoc ⟩
    P • Φ (f (suc n)) ∎

  P-cancel : ∀ {u v : Circuit (₁₊ (₄₊ n))} → P • u ≈ P • v → u ≈ v
  P-cancel {u} {v} e =
    lcancel Γ Ex₂² (lcancel Γ Ex₁² (lcancel Γ Ex²
      (lcancel Γ Ex₃² (lcancel Γ Ex₂² (lcancel Γ Ex₁² (lcancel Γ Ex²
        (trans (sym (spread u)) (trans e (spread v)))))))))
    where
    spread : ∀ w → P • w ≈ Ex ↓ • Ex ↑ • Ex ↑ ↑ • Ex ↑ ↑ ↑ • Ex ↓ • Ex ↑ • Ex ↑ ↑ • w
    spread w = by-passoc (((□ • □ • □ • □) • (□ • □ • □)) • □)
                         (□ • □ • □ • □ • □ • □ • □ • □) Eq.refl

  ----------------------------------------------------------------------
  -- The box wire on wire 3, the fifth wire idle

  Ex₃₄-box₃‴ : Ex ↑ ↑ ↑ • box₃‴ ≈ box₃‴ • Ex ↑ ↑ ↑
  Ex₃₄-box₃‴ = transport Γ P-cancel Ex-P (F-P (λ m → box₃ {m}) (λ m → Eq.refl)) Ex-box₃↑

  Ex₃₄-ΛH₂′ : Ex ↑ ↑ ↑ • ΛH₂′ ≈ ΛH₂′ • Ex ↑ ↑ ↑
  Ex₃₄-ΛH₂′ = transport Γ P-cancel Ex-P (F-P (λ m → ΛH 2 ↓ᵏ m) (λ m → Eq.refl))
                        (S₀₁.⟪⟫-comm (sym eq252))

  Ex₃₄-°ΛH₂′ : Ex ↑ ↑ ↑ • °ΛH₂′ ≈ °ΛH₂′ • Ex ↑ ↑ ↑
  Ex₃₄-°ΛH₂′ = N₂.⟪⟫-≈ Ex₃₄-ΛH₂′ (N₂.⟪⟫-•₂ N₂-Ex₃₄ refl) (N₂.⟪⟫-•₂ refl N₂-Ex₃₄)
    where
    N₂-Ex₃₄ : N₂.⟪ Ex ↑ ↑ ↑ ⟫ ≈ Ex ↑ ↑ ↑
    N₂-Ex₃₄ = N₂.⟪⟫-fix (lemma-cong↑ (X ↑ • Ex ↑ ↑) (Ex ↑ ↑ • X ↑)
                         (lemma-cong↑ (X ↓ • Ex ↑) (Ex ↑ • X ↓) (comm-↓↑ X Ex)))

  ----------------------------------------------------------------------
  -- The swaps on five wires

  far₀₃ : Ex ↓ • Ex ↑ ↑ ↑ ≈ Ex ↑ ↑ ↑ • Ex ↓
  far₀₃ = L-comm Ex (Ex ↑)

  far₁₃ : Ex ↑ • Ex ↑ ↑ ↑ ≈ Ex ↑ ↑ ↑ • Ex ↑
  far₁₃ = lemma-cong↑ (Ex ↓ • Ex ↑ ↑) (Ex ↑ ↑ • Ex ↓) far

  braid₃₄ : Ex ↑ ↑ • Ex ↑ ↑ ↑ • Ex ↑ ↑ ≈ Ex ↑ ↑ ↑ • Ex ↑ ↑ • Ex ↑ ↑ ↑
  braid₃₄ = lemma-cong↑ (Ex ↑ • Ex ↑ ↑ • Ex ↑) (Ex ↑ ↑ • Ex ↑ • Ex ↑ ↑) braid↑

  -- Conjugations by commuting words commute.
  conj-swap : ∀ {x y : Circuit (₁₊ (₄₊ n))} → x • y ≈ y • x → (w : Circuit (₁₊ (₄₊ n))) →
              x • (y • w • y) • x ≈ y • (x • w • x) • y
  conj-swap {x} {y} xy w = begin
    x • (y • w • y) • x       ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
    (x • y) • w • (y • x)     ≈⟨ cong xy (back _ (sym xy)) ⟩
    (y • x) • w • (x • y)     ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    y • (x • w • x) • y ∎

  braid-conj₃₄ : (w : Circuit (₁₊ (₄₊ n))) →
                 S₃₄.⟪ S₂₃.⟪ S₃₄.⟪ w ⟫ ⟫ ⟫ ≈ S₂₃.⟪ S₃₄.⟪ S₂₃.⟪ w ⟫ ⟫ ⟫
  braid-conj₃₄ w = begin
    Ex ↑ ↑ ↑ • (Ex ↑ ↑ • (Ex ↑ ↑ ↑ • w • Ex ↑ ↑ ↑) • Ex ↑ ↑) • Ex ↑ ↑ ↑
      ≈⟨ by-passoc (□ • (□ • (□ • □ • □) • □) • □) ((□ • □ • □) • □ • (□ • □ • □)) Eq.refl ⟩
    (Ex ↑ ↑ ↑ • Ex ↑ ↑ • Ex ↑ ↑ ↑) • w • (Ex ↑ ↑ ↑ • Ex ↑ ↑ • Ex ↑ ↑ ↑)
      ≈⟨ cong (sym braid₃₄) (back _ (sym braid₃₄)) ⟩
    (Ex ↑ ↑ • Ex ↑ ↑ ↑ • Ex ↑ ↑) • w • (Ex ↑ ↑ • Ex ↑ ↑ ↑ • Ex ↑ ↑)
      ≈⟨ by-passoc ((□ • □ • □) • □ • (□ • □ • □)) (□ • (□ • (□ • □ • □) • □) • □) Eq.refl ⟩
    Ex ↑ ↑ • (Ex ↑ ↑ ↑ • (Ex ↑ ↑ • w • Ex ↑ ↑) • Ex ↑ ↑ ↑) • Ex ↑ ↑ ∎

-- A gate at the bottom, pushed through the cycle of the wires 0–3.
push-φ : (F : Circuit (₄₊ n)) → (₄₊ n) ⊢ F • φ ≈ φ • Φ F
push-φ = F-φ

------------------------------------------------------------------------
-- A circuit on the wires 0–3 passes anything on wire 4

L₄-top : (u : Circuit 4) (v : Circuit (₁₊ n)) →
         (₁₊ (₄₊ n)) ⊢ (u ↓ᵏ (₁₊ n)) • v ↑ ↑ ↑ ↑ ≈ v ↑ ↑ ↑ ↑ • (u ↓ᵏ (₁₊ n))
L₄-top [ gate₀ () ]ʷ v
L₄-top [ gate₀ () ↥ ]ʷ v
L₄-top [ gate₀ () ↥ ↥ ]ʷ v
L₄-top [ gate₀ () ↥ ↥ ↥ ]ʷ v
L₄-top [ gate₀ () ↥ ↥ ↥ ↥ ]ʷ v
L₄-top [ gate₁ h ]ʷ v = PB.sym (comm-gate₁-w↑ h (v ↑ ↑ ↑))
L₄-top [ gate₂ h ]ʷ v = PB.sym (comm-gate₂-w↑↑ h (v ↑ ↑))
L₄-top [ gate₁ h ↥ ]ʷ v =
  lemma-cong↑ ([ gate₁ h ]ʷ • v ↑ ↑ ↑) (v ↑ ↑ ↑ • [ gate₁ h ]ʷ) (PB.sym (comm-gate₁-w↑ h (v ↑ ↑)))
L₄-top [ gate₂ h ↥ ]ʷ v =
  lemma-cong↑ ([ gate₂ h ]ʷ • v ↑ ↑ ↑) (v ↑ ↑ ↑ • [ gate₂ h ]ʷ) (PB.sym (comm-gate₂-w↑↑ h (v ↑)))
L₄-top [ gate₁ h ↥ ↥ ]ʷ v =
  lemma-cong↑ ([ gate₁ h ↥ ]ʷ • v ↑ ↑ ↑) (v ↑ ↑ ↑ • [ gate₁ h ↥ ]ʷ)
    (lemma-cong↑ ([ gate₁ h ]ʷ • v ↑ ↑) (v ↑ ↑ • [ gate₁ h ]ʷ) (PB.sym (comm-gate₁-w↑ h (v ↑))))
L₄-top [ gate₂ h ↥ ↥ ]ʷ v =
  lemma-cong↑ ([ gate₂ h ↥ ]ʷ • v ↑ ↑ ↑) (v ↑ ↑ ↑ • [ gate₂ h ↥ ]ʷ)
    (lemma-cong↑ ([ gate₂ h ]ʷ • v ↑ ↑) (v ↑ ↑ • [ gate₂ h ]ʷ) (PB.sym (comm-gate₂-w↑↑ h v)))
L₄-top [ gate₁ h ↥ ↥ ↥ ]ʷ v =
  lemma-cong↑ ([ gate₁ h ↥ ↥ ]ʷ • v ↑ ↑ ↑) (v ↑ ↑ ↑ • [ gate₁ h ↥ ↥ ]ʷ)
    (lemma-cong↑ ([ gate₁ h ↥ ]ʷ • v ↑ ↑) (v ↑ ↑ • [ gate₁ h ↥ ]ʷ)
      (lemma-cong↑ ([ gate₁ h ]ʷ • v ↑) (v ↑ • [ gate₁ h ]ʷ) (PB.sym (comm-gate₁-w↑ h v))))
L₄-top {n} ε v = trans left-unit (sym right-unit)
  where open Tools ((₁₊ (₄₊ n)) VRel,_===_)
L₄-top {n} (u • t) v = begin
  ((u ↓ᵏ (₁₊ n)) • (t ↓ᵏ (₁₊ n))) • v ↑ ↑ ↑ ↑   ≈⟨ assoc ⟩
  (u ↓ᵏ (₁₊ n)) • ((t ↓ᵏ (₁₊ n)) • v ↑ ↑ ↑ ↑)   ≈⟨ back _ (L₄-top t v) ⟩
  (u ↓ᵏ (₁₊ n)) • (v ↑ ↑ ↑ ↑ • (t ↓ᵏ (₁₊ n)))   ≈⟨ sym assoc ⟩
  ((u ↓ᵏ (₁₊ n)) • v ↑ ↑ ↑ ↑) • (t ↓ᵏ (₁₊ n))   ≈⟨ front _ (L₄-top u v) ⟩
  (v ↑ ↑ ↑ ↑ • (u ↓ᵏ (₁₊ n))) • (t ↓ᵏ (₁₊ n))   ≈⟨ assoc ⟩
  v ↑ ↑ ↑ ↑ • (u ↓ᵏ (₁₊ n)) • (t ↓ᵏ (₁₊ n)) ∎
  where open Tools ((₁₊ (₄₊ n)) VRel,_===_)

------------------------------------------------------------------------
-- X and the swap of the wires 3 4

module _ {n : ℕ} where
  private
    Γ = (₁₊ (₄₊ n)) VRel,_===_
  open Tools Γ

  X₀-Ex₃₄ : X ↓ • Ex ↑ ↑ ↑ ≈ Ex ↑ ↑ ↑ • X ↓
  X₀-Ex₃₄ = comm-↓↑ X (Ex ↑ ↑)

  X₁-Ex₃₄ : X ↑ • Ex ↑ ↑ ↑ ≈ Ex ↑ ↑ ↑ • X ↑
  X₁-Ex₃₄ = lemma-cong↑ (X ↓ • Ex ↑ ↑) (Ex ↑ ↑ • X ↓) (comm-↓↑ X (Ex ↑))

  X₂-Ex₃₄ : X ↑ ↑ • Ex ↑ ↑ ↑ ≈ Ex ↑ ↑ ↑ • X ↑ ↑
  X₂-Ex₃₄ = lemma-cong↑ (X ↑ • Ex ↑ ↑) (Ex ↑ ↑ • X ↑)
              (lemma-cong↑ (X ↓ • Ex ↑) (Ex ↑ • X ↓) (comm-↓↑ X Ex))

  -- The swap carries X on wire 4 to X on wire 3, so a gate on the wires
  -- 0–3, moved onto the wires 0 1 2 4, does not see X on wire 3.
  S₃₄-X₄ : S₃₄.⟪ X ↑ ↑ ↑ ↑ ⟫ ≈ X ↑ ↑ ↑
  S₃₄-X₄ = lemma-cong↑ (Ex ↑ ↑ • X ↑ ↑ ↑ • Ex ↑ ↑) (X ↑ ↑)
             (lemma-cong↑ (Ex ↑ • X ↑ ↑ • Ex ↑) (X ↑)
               (lemma-cong↑ (Ex • X ↑ • Ex) (X ↓) S-X↑))

  X₃-S₃₄ : ∀ {w : Circuit (₁₊ (₄₊ n))} → X ↑ ↑ ↑ ↑ • w ≈ w • X ↑ ↑ ↑ ↑ →
           X ↑ ↑ ↑ • S₃₄.⟪ w ⟫ • X ↑ ↑ ↑ ≈ S₃₄.⟪ w ⟫
  X₃-S₃₄ {w} e = begin
    X ↑ ↑ ↑ • S₃₄.⟪ w ⟫ • X ↑ ↑ ↑
      ≈⟨ cong (sym S₃₄-X₄) (back _ (sym S₃₄-X₄)) ⟩
    S₃₄.⟪ X ↑ ↑ ↑ ↑ ⟫ • S₃₄.⟪ w ⟫ • S₃₄.⟪ X ↑ ↑ ↑ ↑ ⟫
      ≈⟨ sym (S₃₄.⟪⟫-•₃ refl refl refl) ⟩
    S₃₄.⟪ X ↑ ↑ ↑ ↑ • w • X ↑ ↑ ↑ ↑ ⟫
      ≈⟨ S₃₄.⟪⟫-cong (trans (sym assoc) (trans (front _ e) (cancelʳ _ X₄²))) ⟩
    S₃₄.⟪ w ⟫ ∎
    where
    X₄² : X ↑ ↑ ↑ ↑ • X ↑ ↑ ↑ ↑ ≈ ε
    X₄² = lemma-cong↑ (X ↑ ↑ ↑ • X ↑ ↑ ↑) ε (lemma-cong↑ (X ↑ ↑ • X ↑ ↑) ε
            (lemma-cong↑ (X ↑ • X ↑) ε (lemma-cong↑ (X • X) ε X²)))
