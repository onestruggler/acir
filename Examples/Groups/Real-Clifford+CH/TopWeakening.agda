------------------------------------------------------------------------
-- Presentations of groups
--
-- An equation between circuits holds under one more wire on top, at
-- every width
--
-- `Weakening` replays a derivation rule by rule, which stops at the
-- schema (19): its box holds every wire of its width, so the rule has
-- no instance with an idle wire on top.  Here the wire is added without
-- looking at the rules: cong↑ puts an idle wire at the bottom, and the
-- cycle σ of swaps that carries wire 0 to the top carries w ↑ to w with
-- the new wire on top — the swap rules (f1)–(f4) of Remark 1 say so for
-- one gate, hence for a circuit.  So
--
--   top-cong :  n ⊢ w ≈ v  →  (1 + n) ⊢ top w ≈ top v
--
-- and in particular (19) holds on the bottom wires of any wider circuit
-- (`box-Z₅` for the five-wire box).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.TopWeakening where

open import Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_ ; wmap)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

import Presentation.Base as PB

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; ax ; Ex²)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- One more wire on top

-- The same gate at the next width.
infixl 8 _↧
_↧ : Gen n → Gen (₁₊ n)
gate₀ h ↧ = gate₀ h
gate₁ h ↧ = gate₁ h
gate₂ h ↧ = gate₂ h
(g ↥)   ↧ = (g ↧) ↥

top : Circuit n → Circuit (₁₊ n)
top = wmap _↧

topᵏ : (k : ℕ) → Circuit n → Circuit (k + n)
topᵏ zero    w = w
topᵏ (suc k) w = top (topᵏ k w)

-- The cycle that carries wire 0 to the top and every other wire one
-- down, and its inverse.
σ σ⁻¹ : (n : ℕ) → Circuit (₁₊ n)
σ zero      = ε
σ (suc n)   = Ex ↓ • σ n ↑
σ⁻¹ zero    = ε
σ⁻¹ (suc n) = σ⁻¹ n ↑ • Ex ↓

------------------------------------------------------------------------
-- The cycle and its inverse

σσ⁻¹ : ∀ n → (₁₊ n) ⊢ σ n • σ⁻¹ n ≈ ε
σσ⁻¹ zero    = PB.left-unit
σσ⁻¹ (suc n) = begin
  (Ex ↓ • σ n ↑) • (σ⁻¹ n ↑ • Ex ↓)     ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
  Ex ↓ • (σ n ↑ • σ⁻¹ n ↑) • Ex ↓       ≈⟨ back _ (front _ (lemma-cong↑ (σ n • σ⁻¹ n) ε (σσ⁻¹ n))) ⟩
  Ex ↓ • ε • Ex ↓                       ≈⟨ back _ left-unit ⟩
  Ex ↓ • Ex ↓                           ≈⟨ Ex² ⟩
  ε ∎
  where open Tools ((₂₊ n) VRel,_===_)

σ⁻¹σ : ∀ n → (₁₊ n) ⊢ σ⁻¹ n • σ n ≈ ε
σ⁻¹σ zero    = PB.left-unit
σ⁻¹σ (suc n) = begin
  (σ⁻¹ n ↑ • Ex ↓) • (Ex ↓ • σ n ↑)     ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
  σ⁻¹ n ↑ • (Ex ↓ • Ex ↓) • σ n ↑       ≈⟨ back _ (front _ Ex²) ⟩
  σ⁻¹ n ↑ • ε • σ n ↑                   ≈⟨ back _ left-unit ⟩
  σ⁻¹ n ↑ • σ n ↑                       ≈⟨ lemma-cong↑ (σ⁻¹ n • σ n) ε (σ⁻¹σ n) ⟩
  ε ∎
  where open Tools ((₂₊ n) VRel,_===_)

------------------------------------------------------------------------
-- Naturality of the cycle

private
  -- A two-wire circuit at the bottom passes anything two wires up.
  low-comm : (u : Circuit 2) (v : Circuit n) → (₂₊ n) ⊢ (u ↓ᵏ n) • v ↑ ↑ ≈ v ↑ ↑ • (u ↓ᵏ n)
  low-comm [ gate₀ () ]ʷ v
  low-comm [ gate₀ () ↥ ]ʷ v
  low-comm [ gate₀ () ↥ ↥ ]ʷ v
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

-- One gate: the rules (f1)–(f4).
nat-gen : (g : Gen n) → (₁₊ n) ⊢ [ g ]ʷ ↑ • σ n ≈ σ n • [ g ↧ ]ʷ
nat-gen (gate₀ ())
nat-gen {suc n} (gate₁ h) = begin
  [ gate₁ h ]ʷ ↑ • Ex ↓ • σ n ↑       ≈⟨ sym assoc ⟩
  ([ gate₁ h ]ʷ ↑ • Ex ↓) • σ n ↑     ≈⟨ front _ (swap₁ h) ⟩
  (Ex ↓ • [ gate₁ h ]ʷ) • σ n ↑       ≈⟨ assoc ⟩
  Ex ↓ • [ gate₁ h ]ʷ • σ n ↑         ≈⟨ back _ (sym (comm-gate₁-w↑ h (σ n))) ⟩
  Ex ↓ • σ n ↑ • [ gate₁ h ]ʷ         ≈⟨ sym assoc ⟩
  (Ex ↓ • σ n ↑) • [ gate₁ h ]ʷ ∎
  where
  open Tools ((₂₊ n) VRel,_===_)
  swap₁ : ∀ h → (₂₊ n) ⊢ [ gate₁ h ]ʷ ↑ • Ex ≈ Ex • [ gate₁ h ]ʷ
  swap₁ H-gate = ax swap-H
  swap₁ Z-gate = ax swap-Z
nat-gen {suc (suc n)} (gate₂ h) = begin
  [ gate₂ h ]ʷ ↑ • Ex ↓ • Ex ↑ • σ n ↑ ↑
    ≈⟨ by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl ⟩
  ([ gate₂ h ]ʷ ↑ • Ex ↓ • Ex ↑) • σ n ↑ ↑
    ≈⟨ front _ (swap₂ h) ⟩
  (Ex ↓ • Ex ↑ • [ gate₂ h ]ʷ) • σ n ↑ ↑
    ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • (□ • □)) Eq.refl ⟩
  Ex ↓ • Ex ↑ • ([ gate₂ h ]ʷ • σ n ↑ ↑)
    ≈⟨ back _ (back _ (sym (comm-gate₂-w↑↑ h (σ n)))) ⟩
  Ex ↓ • Ex ↑ • (σ n ↑ ↑ • [ gate₂ h ]ʷ)
    ≈⟨ by-passoc (□ • □ • (□ • □)) ((□ • □ • □) • □) Eq.refl ⟩
  (Ex ↓ • Ex ↑ • σ n ↑ ↑) • [ gate₂ h ]ʷ ∎
  where
  open Tools ((₃₊ n) VRel,_===_)
  swap₂ : ∀ h → (₃₊ n) ⊢ [ gate₂ h ]ʷ ↑ • Ex ↓ • Ex ↑ ≈ Ex ↓ • Ex ↑ • [ gate₂ h ]ʷ
  swap₂ CZ-gate = ax swap-CZ
  swap₂ CH-gate = ax swap-CH
nat-gen {suc n} (g ↥) = begin
  [ g ]ʷ ↑ ↑ • Ex ↓ • σ n ↑           ≈⟨ sym assoc ⟩
  ([ g ]ʷ ↑ ↑ • Ex ↓) • σ n ↑         ≈⟨ front _ (sym (low-comm Ex [ g ]ʷ)) ⟩
  (Ex ↓ • [ g ]ʷ ↑ ↑) • σ n ↑         ≈⟨ assoc ⟩
  Ex ↓ • [ g ]ʷ ↑ ↑ • σ n ↑           ≈⟨ back _ (lemma-cong↑ ([ g ]ʷ ↑ • σ n) (σ n • [ g ↧ ]ʷ) (nat-gen g)) ⟩
  Ex ↓ • σ n ↑ • [ g ↧ ]ʷ ↑           ≈⟨ sym assoc ⟩
  (Ex ↓ • σ n ↑) • [ g ↧ ]ʷ ↑ ∎
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

------------------------------------------------------------------------
-- The schema (19) on the bottom wires of a wider circuit

-- The (4 + k)-controlled box under m more wires.
box-Z-top : ∀ k m → (m + ₁₊ (₄₊ k)) ⊢ topᵏ m (Z ↓ • Λ□ (₄₊ k)) ≈ topᵏ m (Λ□ (₄₊ k) • Z ↓)
box-Z-top k m = topᵏ-cong m (ax (box-Z k))

-- The five-wire box, in the spelling of the four-qubit development.
box-Z₅ : ∀ m → (₁₊ (₄₊ m)) ⊢ Z ↓ • (Λ□ 4 ↓ᵏ m) ≈ (Λ□ 4 ↓ᵏ m) • Z ↓
box-Z₅ zero    = ax (box-Z 0)
box-Z₅ (suc m) = top-cong (box-Z₅ m)
