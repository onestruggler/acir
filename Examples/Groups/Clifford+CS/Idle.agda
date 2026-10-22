------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 5.1 at any idle wire, as a commutation, and X on an idle wire
-- (Real-Clifford+CH.GeneralN.Idle for the Clifford+CS gates)
--
-- `idle-comm i`: two circuits placed on the wires other than i commute
-- as soon as the circuits one width down do semantically — completeness
-- there, which is the module's hypothesis at the use.  `X-place`: X on
-- the idle wire passes a placed circuit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Idle where

open import Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Semantics using (_~_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.Swaps using (swap-X ; swap-X′ ; facts)
open import Examples.Groups.Clifford+CS.Place
open Laws facts

private
  variable
    n r : ℕ

------------------------------------------------------------------------
-- Lemma 5.1 as a commutation, at the idle wire i

idle-comm : ∀ i → (∀ {u v : Circuit (i +ℕ r)} → ⟦ u ⟧ ~ ⟦ v ⟧ → (i +ℕ r) ⊢ u ≈ v) →
            ∀ {X Y : Circuit (i +ℕ r)} {a b : Circuit (₁₊ (i +ℕ r))} →
            (₁₊ (i +ℕ r)) ⊢ place i X ≈ a → (₁₊ (i +ℕ r)) ⊢ place i Y ≈ b →
            ⟦ X • Y ⟧ ~ ⟦ Y • X ⟧ → (₁₊ (i +ℕ r)) ⊢ a • b ≈ b • a
idle-comm {r} i complete {X} {Y} {a} {b} ea eb e = begin
  a • b                      ≈⟨ cong (sym ea) (sym eb) ⟩
  place i X • place i Y      ≈⟨ sym (place-• i X Y) ⟩
  place i (X • Y)            ≈⟨ lemma-5-1 i complete e ⟩
  place i (Y • X)            ≈⟨ place-• i Y X ⟩
  place i Y • place i X      ≈⟨ cong eb ea ⟩
  b • a ∎
  where open Tools ((₁₊ (i +ℕ r)) VRel,_===_)

------------------------------------------------------------------------
-- X on an idle wire passes a placed circuit

-- A one-wire circuit at the bottom passes anything one wire up.
low₁-comm : (u : Circuit 1) (v : Circuit n) → (₁₊ n) ⊢ (u ↓ᵏ n) • v ↑ ≈ v ↑ • (u ↓ᵏ n)
low₁-comm {n} [ gate₀ h ]ʷ v = PB.sym (comm-gate₀-w h (v ↑))
low₁-comm {n} [ gate₀ h ↥ ]ʷ v = lemma-cong↑ ([ gate₀ h ]ʷ • v) (v • [ gate₀ h ]ʷ) (PB.sym (comm-gate₀-w h v))
low₁-comm {n} [ gate₁ h ]ʷ v = PB.sym (comm-gate₁-w↑ h v)
low₁-comm {n} ε v = trans left-unit (sym right-unit)
  where open Tools ((₁₊ n) VRel,_===_)
low₁-comm {n} (u • t) v = begin
  ((u ↓ᵏ n) • (t ↓ᵏ n)) • v ↑   ≈⟨ assoc ⟩
  (u ↓ᵏ n) • ((t ↓ᵏ n) • v ↑)   ≈⟨ back _ (low₁-comm t v) ⟩
  (u ↓ᵏ n) • (v ↑ • (t ↓ᵏ n))   ≈⟨ sym assoc ⟩
  ((u ↓ᵏ n) • v ↑) • (t ↓ᵏ n)   ≈⟨ front _ (low₁-comm u v) ⟩
  (v ↑ • (u ↓ᵏ n)) • (t ↓ᵏ n)   ≈⟨ assoc ⟩
  v ↑ • (u ↓ᵏ n) • (t ↓ᵏ n) ∎
  where open Tools ((₁₊ n) VRel,_===_)

-- X on wire 0 passes anything one wire up.
X-↑ : ∀ (u : Circuit n) → (₁₊ n) ⊢ X • u ↑ ≈ u ↑ • X
X-↑ u = low₁-comm X u

-- X on wire i.
Xᵢ : (i : ℕ) → Circuit (₁₊ (i +ℕ r))
Xᵢ zero    = X
Xᵢ (suc i) = Xᵢ i ↑

X-cyc⁻¹ : ∀ i → (₁₊ (i +ℕ r)) ⊢ Xᵢ i • cyc⁻¹ i ≈ cyc⁻¹ i • X
X-cyc⁻¹ {r} zero = trans right-unit (sym left-unit)
  where open Tools ((₁₊ r) VRel,_===_)
X-cyc⁻¹ {r} (suc i) = begin
  Xᵢ i ↑ • (cyc⁻¹ i ↑ • Swap)     ≈⟨ sym assoc ⟩
  (Xᵢ i ↑ • cyc⁻¹ i ↑) • Swap     ≈⟨ front _ (lemma-cong↑ (Xᵢ i • cyc⁻¹ i) (cyc⁻¹ i • X) (X-cyc⁻¹ i)) ⟩
  (cyc⁻¹ i ↑ • X ↑) • Swap        ≈⟨ trans assoc (back _ swap-X) ⟩
  cyc⁻¹ i ↑ • (Swap • X)          ≈⟨ sym assoc ⟩
  (cyc⁻¹ i ↑ • Swap) • X ∎
  where open Tools ((₂₊ (i +ℕ r)) VRel,_===_)

cyc-X : ∀ i → (₁₊ (i +ℕ r)) ⊢ cyc i • Xᵢ i ≈ X • cyc i
cyc-X {r} zero = trans left-unit (sym right-unit)
  where open Tools ((₁₊ r) VRel,_===_)
cyc-X {r} (suc i) = begin
  (Swap • cyc i ↑) • Xᵢ i ↑       ≈⟨ assoc ⟩
  Swap • (cyc i ↑ • Xᵢ i ↑)       ≈⟨ back _ (lemma-cong↑ (cyc i • Xᵢ i) (X • cyc i) (cyc-X i)) ⟩
  Swap • (X ↑ • cyc i ↑)          ≈⟨ trans (sym assoc) (front _ swap-X′) ⟩
  (X • Swap) • cyc i ↑            ≈⟨ assoc ⟩
  X • (Swap • cyc i ↑) ∎
  where open Tools ((₂₊ (i +ℕ r)) VRel,_===_)

X-place : ∀ i (u : Circuit (i +ℕ r)) → (₁₊ (i +ℕ r)) ⊢ Xᵢ i • place i u ≈ place i u • Xᵢ i
X-place {r} i u = begin
  Xᵢ i • (cyc⁻¹ i • u ↑ • cyc i)   ≈⟨ sym assoc ⟩
  (Xᵢ i • cyc⁻¹ i) • u ↑ • cyc i   ≈⟨ front _ (X-cyc⁻¹ i) ⟩
  (cyc⁻¹ i • X) • u ↑ • cyc i      ≈⟨ trans assoc (back _ (trans (sym assoc) (front _ (X-↑ u)))) ⟩
  cyc⁻¹ i • (u ↑ • X) • cyc i      ≈⟨ back _ (trans assoc (back _ (sym (cyc-X i)))) ⟩
  cyc⁻¹ i • u ↑ • (cyc i • Xᵢ i)   ≈⟨ by-passoc (□ • □ • (□ • □)) ((□ • □ • □) • □) Eq.refl ⟩
  (cyc⁻¹ i • u ↑ • cyc i) • Xᵢ i ∎
  where open Tools ((₁₊ (i +ℕ r)) VRel,_===_)
