------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 5.1 at any idle wire, and the box B one wire up placed with
-- its idle wire 3 removed
--
-- `idle-comm i`: two circuits placed on the wires other than i commute
-- as soon as the circuits one width down do semantically — completeness
-- there, which is the module's hypothesis at the use.  The box B = B□ k
-- one wire up has two idle wires, 0 and 3; with wire 3 removed it is
-- the box on wire 2 with its first control on wire 1, `yB k`, and
-- `place-yB` says so: the two networks that carry wire 3 to wire 0
-- around it have the same permutation up to a swap below it (PermCalc).
-- `cf-yB` is its controlled form, for the semantic side of such steps.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Idle where

open import Data.Fin using (zero ; suc)
open import Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; Ex² ; ax)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CForm
open import Examples.Groups.Real-Clifford+CH.GeneralN.Locals using (Ex₁₂ᴸ ; Ex₁₂ᴸ-def)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Sem using (B□ ; cf-Λ↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place
open import Examples.Groups.Real-Clifford+CH.GeneralN.Networks using (scyc ; scyc⁻¹)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (perm-≈)

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
-- B one wire up, with its idle wire 3 removed

yB : ∀ k → Circuit (₄₊ k)
yB k = Ex ↑ • Λ□ (₂₊ k) ↑ • Ex ↑

cf-yB : ∀ k → CF {3} {₁₊ k} (yB k)
cf-yB k = cf-• (cf-loc′ (Ex ↑) Ex₁₂ᴸ Ex₁₂ᴸ-def) (cf-• (cf-Λ↑ k) (cf-loc′ (Ex ↑) Ex₁₂ᴸ Ex₁₂ᴸ-def))

module _ (k : ℕ) where

  private
    open Tools ((₁₊ (₄₊ k)) VRel,_===_)

    N≈ : (₁₊ (₄₊ k)) ⊢ cyc⁻¹ 3 • Ex ↑ ↑ ≈ τ₀₂ ↑ • Ex ↓
    N≈ = perm-≈ {u = scyc⁻¹ 3 • (S.σ S.↑) S.↑} {v = (S.σ • S.σ S.↑ • S.σ) S.↑ • S.σ}
           (λ { zero → Eq.refl ; (suc zero) → Eq.refl ; (suc (suc zero)) → Eq.refl
              ; (suc (suc (suc zero))) → Eq.refl ; (suc (suc (suc (suc _)))) → Eq.refl })

    M≈ : (₁₊ (₄₊ k)) ⊢ Ex ↑ ↑ • cyc 3 ≈ Ex ↓ • τ₀₂ ↑
    M≈ = perm-≈ {u = (S.σ S.↑) S.↑ • scyc 3} {v = S.σ • (S.σ • S.σ S.↑ • S.σ) S.↑}
           (λ { zero → Eq.refl ; (suc zero) → Eq.refl ; (suc (suc zero)) → Eq.refl
              ; (suc (suc (suc zero))) → Eq.refl ; (suc (suc (suc (suc _)))) → Eq.refl })

    Λ₂↑ : Circuit (₁₊ (₄₊ k))
    Λ₂↑ = Λ□ (₂₊ k) ↑ ↑

  place-yB : (₁₊ (₄₊ k)) ⊢ place 3 (yB k) ≈ B□ k ↑
  place-yB = begin
    cyc⁻¹ 3 • (Ex ↑ ↑ • Λ₂↑ • Ex ↑ ↑) • cyc 3
      ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
    (cyc⁻¹ 3 • Ex ↑ ↑) • Λ₂↑ • (Ex ↑ ↑ • cyc 3)
      ≈⟨ cong N≈ (back _ M≈) ⟩
    (τ₀₂ ↑ • Ex ↓) • Λ₂↑ • (Ex ↓ • τ₀₂ ↑)
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □) • □ • □) Eq.refl ⟩
    τ₀₂ ↑ • (Ex ↓ • Λ₂↑) • Ex ↓ • τ₀₂ ↑
      ≈⟨ back _ (front _ (low-comm Ex (Λ□ (₂₊ k)))) ⟩
    τ₀₂ ↑ • (Λ₂↑ • Ex ↓) • Ex ↓ • τ₀₂ ↑
      ≈⟨ by-passoc (□ • (□ • □) • □ • □) (□ • □ • (□ • □) • □) Eq.refl ⟩
    τ₀₂ ↑ • Λ₂↑ • (Ex ↓ • Ex ↓) • τ₀₂ ↑
      ≈⟨ back _ (back _ (front _ Ex²)) ⟩
    τ₀₂ ↑ • Λ₂↑ • ε • τ₀₂ ↑
      ≈⟨ back _ (back _ left-unit) ⟩
    τ₀₂ ↑ • Λ₂↑ • τ₀₂ ↑ ∎

------------------------------------------------------------------------
-- Two idle wires, placed in either order

-- A circuit with the wires 2 3 idle, placed by inserting wire 2 twice
-- or wire 3 after wire 2: the two networks differ by the swap of the
-- two idle wires, which passes the circuit lifted two wires.
module _ {r : ℕ} (z : Circuit (2 +ℕ r)) where

  private
    open Tools ((₄₊ r) VRel,_===_)

    N≈ : (₄₊ r) ⊢ cyc⁻¹ 3 • cyc⁻¹ 2 ↑ ≈ (cyc⁻¹ 2 • cyc⁻¹ 2 ↑) • Ex ↓
    N≈ = perm-≈ {u = scyc⁻¹ 3 • (scyc⁻¹ 2) S.↑} {v = (scyc⁻¹ 2 • (scyc⁻¹ 2) S.↑) • S.σ}
           (λ { zero → Eq.refl ; (suc zero) → Eq.refl ; (suc (suc zero)) → Eq.refl
              ; (suc (suc (suc zero))) → Eq.refl ; (suc (suc (suc (suc _)))) → Eq.refl })

    M≈ : (₄₊ r) ⊢ cyc 2 ↑ • cyc 3 ≈ Ex ↓ • (cyc 2 ↑ • cyc 2)
    M≈ = perm-≈ {u = (scyc 2) S.↑ • scyc 3} {v = S.σ • ((scyc 2) S.↑ • scyc 2)}
           (λ { zero → Eq.refl ; (suc zero) → Eq.refl ; (suc (suc zero)) → Eq.refl
              ; (suc (suc (suc zero))) → Eq.refl ; (suc (suc (suc (suc _)))) → Eq.refl })

  place-swap : (₄₊ r) ⊢ place 2 (place 2 z) ≈ place 3 (place 2 z)
  place-swap = begin
    cyc⁻¹ 2 • (cyc⁻¹ 2 ↑ • z ↑ ↑ • cyc 2 ↑) • cyc 2
      ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
    (cyc⁻¹ 2 • cyc⁻¹ 2 ↑) • z ↑ ↑ • (cyc 2 ↑ • cyc 2)
      ≈⟨ back _ (back _ (sym (trans (front _ Ex²) left-unit))) ⟩
    (cyc⁻¹ 2 • cyc⁻¹ 2 ↑) • z ↑ ↑ • ((Ex ↓ • Ex ↓) • cyc 2 ↑ • cyc 2)
      ≈⟨ by-passoc ((□ • □) • □ • ((□ • □) • □ • □)) ((□ • □) • □ • □ • (□ • □ • □)) Eq.refl ⟩
    (cyc⁻¹ 2 • cyc⁻¹ 2 ↑) • z ↑ ↑ • Ex ↓ • (Ex ↓ • cyc 2 ↑ • cyc 2)
      ≈⟨ back _ (trans (sym assoc) (front _ (sym (low-comm Ex z)))) ⟩
    (cyc⁻¹ 2 • cyc⁻¹ 2 ↑) • (Ex ↓ • z ↑ ↑) • (Ex ↓ • cyc 2 ↑ • cyc 2)
      ≈⟨ by-passoc ((□ • □) • (□ • □) • (□ • □ • □)) (((□ • □) • □) • □ • (□ • (□ • □))) Eq.refl ⟩
    ((cyc⁻¹ 2 • cyc⁻¹ 2 ↑) • Ex ↓) • z ↑ ↑ • (Ex ↓ • (cyc 2 ↑ • cyc 2))
      ≈⟨ cong (sym N≈) (back _ (sym M≈)) ⟩
    (cyc⁻¹ 3 • cyc⁻¹ 2 ↑) • z ↑ ↑ • (cyc 2 ↑ • cyc 3)
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    cyc⁻¹ 3 • (cyc⁻¹ 2 ↑ • z ↑ ↑ • cyc 2 ↑) • cyc 3 ∎

  -- The swap of the two idle wires passes the circuit.
  private
    N₂₃ : (₄₊ r) ⊢ Ex ↑ ↑ • (cyc⁻¹ 2 • cyc⁻¹ 2 ↑) ≈ (cyc⁻¹ 2 • cyc⁻¹ 2 ↑) • Ex ↓
    N₂₃ = perm-≈ {u = (S.σ S.↑) S.↑ • (scyc⁻¹ 2 • (scyc⁻¹ 2) S.↑)} {v = (scyc⁻¹ 2 • (scyc⁻¹ 2) S.↑) • S.σ}
            (λ { zero → Eq.refl ; (suc zero) → Eq.refl ; (suc (suc zero)) → Eq.refl
               ; (suc (suc (suc zero))) → Eq.refl ; (suc (suc (suc (suc _)))) → Eq.refl })

    M₂₃ : (₄₊ r) ⊢ Ex ↓ • (cyc 2 ↑ • cyc 2) ≈ (cyc 2 ↑ • cyc 2) • Ex ↑ ↑
    M₂₃ = perm-≈ {u = S.σ • ((scyc 2) S.↑ • scyc 2)} {v = ((scyc 2) S.↑ • scyc 2) • (S.σ S.↑) S.↑}
            (λ { zero → Eq.refl ; (suc zero) → Eq.refl ; (suc (suc zero)) → Eq.refl
               ; (suc (suc (suc zero))) → Eq.refl ; (suc (suc (suc (suc _)))) → Eq.refl })

  swap-idle₂₃ : (₄₊ r) ⊢ Ex ↑ ↑ • place 2 (place 2 z) ≈ place 2 (place 2 z) • Ex ↑ ↑
  swap-idle₂₃ = begin
    Ex ↑ ↑ • (cyc⁻¹ 2 • (cyc⁻¹ 2 ↑ • z ↑ ↑ • cyc 2 ↑) • cyc 2)
      ≈⟨ by-passoc (□ • (□ • (□ • □ • □) • □)) ((□ • (□ • □)) • □ • (□ • □)) Eq.refl ⟩
    (Ex ↑ ↑ • (cyc⁻¹ 2 • cyc⁻¹ 2 ↑)) • z ↑ ↑ • (cyc 2 ↑ • cyc 2)
      ≈⟨ front _ N₂₃ ⟩
    ((cyc⁻¹ 2 • cyc⁻¹ 2 ↑) • Ex ↓) • z ↑ ↑ • (cyc 2 ↑ • cyc 2)
      ≈⟨ by-passoc (((□ • □) • □) • □ • (□ • □)) ((□ • □) • (□ • □) • (□ • □)) Eq.refl ⟩
    (cyc⁻¹ 2 • cyc⁻¹ 2 ↑) • (Ex ↓ • z ↑ ↑) • (cyc 2 ↑ • cyc 2)
      ≈⟨ back _ (front _ (low-comm Ex z)) ⟩
    (cyc⁻¹ 2 • cyc⁻¹ 2 ↑) • (z ↑ ↑ • Ex ↓) • (cyc 2 ↑ • cyc 2)
      ≈⟨ by-passoc ((□ • □) • (□ • □) • (□ • □)) ((□ • □) • □ • (□ • (□ • □))) Eq.refl ⟩
    (cyc⁻¹ 2 • cyc⁻¹ 2 ↑) • z ↑ ↑ • (Ex ↓ • (cyc 2 ↑ • cyc 2))
      ≈⟨ back _ (back _ M₂₃) ⟩
    (cyc⁻¹ 2 • cyc⁻¹ 2 ↑) • z ↑ ↑ • ((cyc 2 ↑ • cyc 2) • Ex ↑ ↑)
      ≈⟨ by-passoc ((□ • □) • □ • ((□ • □) • □)) ((□ • (□ • □ • □) • □) • □) Eq.refl ⟩
    (cyc⁻¹ 2 • (cyc⁻¹ 2 ↑ • z ↑ ↑ • cyc 2 ↑) • cyc 2) • Ex ↑ ↑ ∎

------------------------------------------------------------------------
-- X on an idle wire passes a placed circuit

-- X on wire i.
Xᵢ : (i : ℕ) → Circuit (₁₊ (i +ℕ r))
Xᵢ zero    = X
Xᵢ (suc i) = Xᵢ i ↑

-- X through the swap, by the swap rules.
swapX : (₂₊ n) ⊢ X ↑ • Ex ↓ ≈ Ex ↓ • X ↓
swapX {n} = begin
  (H ↑ • Z ↑ • H ↑) • Ex     ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • (□ • □)) Eq.refl ⟩
  H ↑ • Z ↑ • (H ↑ • Ex)     ≈⟨ back _ (back _ (ax swap-H)) ⟩
  H ↑ • Z ↑ • (Ex • H)       ≈⟨ back _ (trans (sym assoc) (front _ (ax swap-Z))) ⟩
  H ↑ • (Ex • Z) • H         ≈⟨ trans (sym assoc) (front _ (trans (sym assoc) (front _ (ax swap-H)))) ⟩
  ((Ex • H) • Z) • H         ≈⟨ by-passoc (((□ • □) • □) • □) (□ • □ • □ • □) Eq.refl ⟩
  Ex • H • Z • H ∎
  where open Tools ((₂₊ n) VRel,_===_)

swapX′ : (₂₊ n) ⊢ Ex ↓ • X ↑ ≈ X ↓ • Ex ↓
swapX′ {n} = begin
  Ex • X ↑                   ≈⟨ sym right-unit ⟩
  (Ex • X ↑) • ε             ≈⟨ back _ (sym Ex²) ⟩
  (Ex • X ↑) • (Ex • Ex)     ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
  Ex • (X ↑ • Ex) • Ex       ≈⟨ back _ (front _ swapX) ⟩
  Ex • (Ex • X) • Ex         ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
  (Ex • Ex) • X • Ex         ≈⟨ trans (front _ Ex²) left-unit ⟩
  X • Ex ∎
  where open Tools ((₂₊ n) VRel,_===_)

-- X on wire 0 passes anything one wire up.
X-↑ : ∀ (u : Circuit n) → (₁₊ n) ⊢ X • u ↑ ≈ u ↑ • X
X-↑ {n} u = begin
  (H • Z • H) • u ↑         ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • (□ • □)) Eq.refl ⟩
  H • Z • (H • u ↑)         ≈⟨ back _ (back _ (sym (comm-gate₁-w↑ H-gate u))) ⟩
  H • Z • (u ↑ • H)         ≈⟨ back _ (trans (sym assoc) (front _ (sym (comm-gate₁-w↑ Z-gate u)))) ⟩
  H • (u ↑ • Z) • H         ≈⟨ trans (sym assoc) (front _ (trans (sym assoc) (front _ (sym (comm-gate₁-w↑ H-gate u))))) ⟩
  ((u ↑ • H) • Z) • H       ≈⟨ by-passoc (((□ • □) • □) • □) (□ • (□ • □ • □)) Eq.refl ⟩
  u ↑ • (H • Z • H) ∎
  where open Tools ((₁₊ n) VRel,_===_)

X-cyc⁻¹ : ∀ i → (₁₊ (i +ℕ r)) ⊢ Xᵢ i • cyc⁻¹ i ≈ cyc⁻¹ i • X
X-cyc⁻¹ {r} zero = trans right-unit (sym left-unit)
  where open Tools ((₁₊ r) VRel,_===_)
X-cyc⁻¹ {r} (suc i) = begin
  Xᵢ i ↑ • (cyc⁻¹ i ↑ • Ex ↓)     ≈⟨ sym assoc ⟩
  (Xᵢ i ↑ • cyc⁻¹ i ↑) • Ex ↓     ≈⟨ front _ (lemma-cong↑ (Xᵢ i • cyc⁻¹ i) (cyc⁻¹ i • X) (X-cyc⁻¹ i)) ⟩
  (cyc⁻¹ i ↑ • X ↑) • Ex ↓        ≈⟨ trans assoc (back _ swapX) ⟩
  cyc⁻¹ i ↑ • (Ex ↓ • X ↓)        ≈⟨ sym assoc ⟩
  (cyc⁻¹ i ↑ • Ex ↓) • X ∎
  where open Tools ((₂₊ (i +ℕ r)) VRel,_===_)

cyc-X : ∀ i → (₁₊ (i +ℕ r)) ⊢ cyc i • Xᵢ i ≈ X • cyc i
cyc-X {r} zero = trans left-unit (sym right-unit)
  where open Tools ((₁₊ r) VRel,_===_)
cyc-X {r} (suc i) = begin
  (Ex ↓ • cyc i ↑) • Xᵢ i ↑       ≈⟨ assoc ⟩
  Ex ↓ • (cyc i ↑ • Xᵢ i ↑)       ≈⟨ back _ (lemma-cong↑ (cyc i • Xᵢ i) (X • cyc i) (cyc-X i)) ⟩
  Ex ↓ • (X ↑ • cyc i ↑)          ≈⟨ trans (sym assoc) (front _ swapX′) ⟩
  (X ↓ • Ex ↓) • cyc i ↑          ≈⟨ assoc ⟩
  X • (Ex ↓ • cyc i ↑) ∎
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
