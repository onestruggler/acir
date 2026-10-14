------------------------------------------------------------------------
-- Presentations of groups
--
-- An equation between circuits holds under one more wire on top, at
-- every width (Real-Clifford+CH.TopWeakening for the Clifford+CS gates)
--
-- Weakening replays a derivation rule by rule; here the wire is added
-- without looking at the rules: cong↑ puts an idle wire at the bottom,
-- and the cycle σ of swaps that carries wire 0 to the top carries w ↑
-- to w with the new wire on top — the swap rules (Swaps) say so for one
-- gate, hence for a circuit.  So
--
--   top-cong :  n ⊢ w ≈ v  →  (1 + n) ⊢ top w ≈ top v.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.TopWeakening where

open import Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (_↧ ; top)
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.Swaps using (Swap² ; swap₁ ; swap₂)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- More wires on top

topᵏ : (k : ℕ) → Circuit n → Circuit (k + n)
topᵏ zero    w = w
topᵏ (suc k) w = top (topᵏ k w)

-- The cycle that carries wire 0 to the top and every other wire one
-- down, and its inverse.
σ σ⁻¹ : (n : ℕ) → Circuit (₁₊ n)
σ zero      = ε
σ (suc n)   = Swap • σ n ↑
σ⁻¹ zero    = ε
σ⁻¹ (suc n) = σ⁻¹ n ↑ • Swap

------------------------------------------------------------------------
-- The cycle and its inverse

σσ⁻¹ : ∀ n → (₁₊ n) ⊢ σ n • σ⁻¹ n ≈ ε
σσ⁻¹ zero    = PB.left-unit
σσ⁻¹ (suc n) = begin
  (Swap • σ n ↑) • (σ⁻¹ n ↑ • Swap)     ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
  Swap • (σ n ↑ • σ⁻¹ n ↑) • Swap       ≈⟨ back _ (front _ (lemma-cong↑ (σ n • σ⁻¹ n) ε (σσ⁻¹ n))) ⟩
  Swap • ε • Swap                       ≈⟨ back _ left-unit ⟩
  Swap • Swap                           ≈⟨ Swap² ⟩
  ε ∎
  where open Tools ((₂₊ n) VRel,_===_)

σ⁻¹σ : ∀ n → (₁₊ n) ⊢ σ⁻¹ n • σ n ≈ ε
σ⁻¹σ zero    = PB.left-unit
σ⁻¹σ (suc n) = begin
  (σ⁻¹ n ↑ • Swap) • (Swap • σ n ↑)     ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
  σ⁻¹ n ↑ • (Swap • Swap) • σ n ↑       ≈⟨ back _ (front _ Swap²) ⟩
  σ⁻¹ n ↑ • ε • σ n ↑                   ≈⟨ back _ left-unit ⟩
  σ⁻¹ n ↑ • σ n ↑                       ≈⟨ lemma-cong↑ (σ⁻¹ n • σ n) ε (σ⁻¹σ n) ⟩
  ε ∎
  where open Tools ((₂₊ n) VRel,_===_)

------------------------------------------------------------------------
-- A two-wire circuit at the bottom passes anything two wires up

low-comm : (u : Circuit 2) (v : Circuit n) → (₂₊ n) ⊢ (u ↓ᵏ n) • v ↑ ↑ ≈ v ↑ ↑ • (u ↓ᵏ n)
low-comm {n} [ gate₀ h ]ʷ v = PB.sym (comm-gate₀-w h (v ↑ ↑))
low-comm {n} [ gate₀ h ↥ ]ʷ v =
  lemma-cong↑ ([ gate₀ h ]ʷ • v ↑) (v ↑ • [ gate₀ h ]ʷ) (PB.sym (comm-gate₀-w h (v ↑)))
low-comm {n} [ gate₀ h ↥ ↥ ]ʷ v =
  lemma-cong↑ ([ gate₀ h ↥ ]ʷ • v ↑) (v ↑ • [ gate₀ h ↥ ]ʷ)
    (lemma-cong↑ ([ gate₀ h ]ʷ • v) (v • [ gate₀ h ]ʷ) (PB.sym (comm-gate₀-w h v)))
low-comm {n} [ gate₁ h ]ʷ v = sym (comm-gate₁-w↑ h (v ↑))
  where open Tools ((₂₊ n) VRel,_===_)
low-comm {n} [ gate₂ h ]ʷ v = sym (comm-gate₂-w↑↑ h v)
  where open Tools ((₂₊ n) VRel,_===_)
low-comm {n} [ gate₁ h ↥ ]ʷ v =
  lemma-cong↑ ([ gate₁ h ]ʷ • v ↑) (v ↑ • [ gate₁ h ]ʷ) (PB-sym (comm-gate₁-w↑ h v))
  where open Tools ((₁₊ n) VRel,_===_) renaming (sym to PB-sym)
low-comm {n} ε v = trans left-unit (sym right-unit)
  where open Tools ((₂₊ n) VRel,_===_)
low-comm {n} (u • t) v = begin
  ((u ↓ᵏ n) • (t ↓ᵏ n)) • v ↑ ↑   ≈⟨ assoc ⟩
  (u ↓ᵏ n) • ((t ↓ᵏ n) • v ↑ ↑)   ≈⟨ back _ (low-comm t v) ⟩
  (u ↓ᵏ n) • (v ↑ ↑ • (t ↓ᵏ n))   ≈⟨ sym assoc ⟩
  ((u ↓ᵏ n) • v ↑ ↑) • (t ↓ᵏ n)   ≈⟨ front _ (low-comm u v) ⟩
  (v ↑ ↑ • (u ↓ᵏ n)) • (t ↓ᵏ n)   ≈⟨ assoc ⟩
  v ↑ ↑ • (u ↓ᵏ n) • (t ↓ᵏ n) ∎
  where open Tools ((₂₊ n) VRel,_===_)

------------------------------------------------------------------------
-- Naturality of the cycle

-- One gate: the scalar by its own rule, the others by the swap rules.
nat-gen : (g : Gen n) → (₁₊ n) ⊢ [ g ]ʷ ↑ • σ n ≈ σ n • [ g ↧ ]ʷ
nat-gen {n} (gate₀ h) = trans (front (σ n) (PB.axiom (ω↑=ω h))) (sym (comm-gate₀-w h (σ n)))
  where open Tools ((₁₊ n) VRel,_===_)
nat-gen {suc n} (gate₁ h) = begin
  [ gate₁ h ]ʷ ↑ • Swap • σ n ↑       ≈⟨ sym assoc ⟩
  ([ gate₁ h ]ʷ ↑ • Swap) • σ n ↑     ≈⟨ front _ (swap₁ h) ⟩
  (Swap • [ gate₁ h ]ʷ) • σ n ↑       ≈⟨ assoc ⟩
  Swap • [ gate₁ h ]ʷ • σ n ↑         ≈⟨ back _ (sym (comm-gate₁-w↑ h (σ n))) ⟩
  Swap • σ n ↑ • [ gate₁ h ]ʷ         ≈⟨ sym assoc ⟩
  (Swap • σ n ↑) • [ gate₁ h ]ʷ ∎
  where open Tools ((₂₊ n) VRel,_===_)
nat-gen {suc (suc n)} (gate₂ h) = begin
  [ gate₂ h ]ʷ ↑ • Swap • Swap ↑ • σ n ↑ ↑
    ≈⟨ by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl ⟩
  ([ gate₂ h ]ʷ ↑ • Swap • Swap ↑) • σ n ↑ ↑
    ≈⟨ front _ (swap₂ h) ⟩
  (Swap • Swap ↑ • [ gate₂ h ]ʷ) • σ n ↑ ↑
    ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • (□ • □)) Eq.refl ⟩
  Swap • Swap ↑ • ([ gate₂ h ]ʷ • σ n ↑ ↑)
    ≈⟨ back _ (back _ (sym (comm-gate₂-w↑↑ h (σ n)))) ⟩
  Swap • Swap ↑ • (σ n ↑ ↑ • [ gate₂ h ]ʷ)
    ≈⟨ by-passoc (□ • □ • (□ • □)) ((□ • □ • □) • □) Eq.refl ⟩
  (Swap • Swap ↑ • σ n ↑ ↑) • [ gate₂ h ]ʷ ∎
  where open Tools ((₃₊ n) VRel,_===_)
nat-gen {suc n} (g ↥) = begin
  [ g ]ʷ ↑ ↑ • Swap • σ n ↑           ≈⟨ sym assoc ⟩
  ([ g ]ʷ ↑ ↑ • Swap) • σ n ↑         ≈⟨ front _ (sym (low-comm Swap [ g ]ʷ)) ⟩
  (Swap • [ g ]ʷ ↑ ↑) • σ n ↑         ≈⟨ assoc ⟩
  Swap • [ g ]ʷ ↑ ↑ • σ n ↑           ≈⟨ back _ (lemma-cong↑ ([ g ]ʷ ↑ • σ n) (σ n • [ g ↧ ]ʷ) (nat-gen g)) ⟩
  Swap • σ n ↑ • [ g ↧ ]ʷ ↑           ≈⟨ sym assoc ⟩
  (Swap • σ n ↑) • [ g ↧ ]ʷ ↑ ∎
  where open Tools ((₂₊ n) VRel,_===_)

-- A circuit.
nat : (w : Circuit n) → (₁₊ n) ⊢ w ↑ • σ n ≈ σ n • top w
nat [ g ]ʷ = nat-gen g
nat {n} ε = trans left-unit (sym right-unit)
  where open Tools ((₁₊ n) VRel,_===_)
nat {n} (w • v) = begin
  (w ↑ • v ↑) • σ n         ≈⟨ assoc ⟩
  w ↑ • (v ↑ • σ n)         ≈⟨ back _ (nat v) ⟩
  w ↑ • (σ n • top v)       ≈⟨ sym assoc ⟩
  (w ↑ • σ n) • top v       ≈⟨ front _ (nat w) ⟩
  (σ n • top w) • top v     ≈⟨ assoc ⟩
  σ n • top w • top v ∎
  where open Tools ((₁₊ n) VRel,_===_)

------------------------------------------------------------------------
-- Weakening

top-cong : ∀ {w v : Circuit n} → n ⊢ w ≈ v → (₁₊ n) ⊢ top w ≈ top v
top-cong {n} {w} {v} e = begin
  top w                     ≈⟨ sym left-unit ⟩
  ε • top w                 ≈⟨ front _ (sym (σ⁻¹σ n)) ⟩
  (σ⁻¹ n • σ n) • top w     ≈⟨ assoc ⟩
  σ⁻¹ n • (σ n • top w)     ≈⟨ back _ (sym (nat w)) ⟩
  σ⁻¹ n • (w ↑ • σ n)       ≈⟨ back _ (front _ (lemma-cong↑ w v e)) ⟩
  σ⁻¹ n • (v ↑ • σ n)       ≈⟨ back _ (nat v) ⟩
  σ⁻¹ n • (σ n • top v)     ≈⟨ sym assoc ⟩
  (σ⁻¹ n • σ n) • top v     ≈⟨ front _ (σ⁻¹σ n) ⟩
  ε • top v                 ≈⟨ left-unit ⟩
  top v ∎
  where open Tools ((₁₊ n) VRel,_===_)

topᵏ-cong : ∀ k {w v : Circuit n} → n ⊢ w ≈ v → (k + n) ⊢ topᵏ k w ≈ topᵏ k v
topᵏ-cong zero    e = e
topᵏ-cong (suc k) e = top-cong (topᵏ-cong k e)
