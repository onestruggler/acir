------------------------------------------------------------------------
-- Presentations of groups
--
-- An n-wire circuit placed on the n + 1 wires other than one, and
-- Lemma 5.1
--
-- Lemma 5.1 is completeness one width down: two circuits that leave
-- the same wire idle and have the same semantics are equal.  With the
-- idle wire i, a circuit u of the smaller width sits on the other
-- wires, in order, as
--
--     place i u  =  cyc⁻¹ i • u ↑ • cyc i,
--
-- cyc i being the cycle of the bottom i + 1 wires that carries wire 0
-- up to wire i.  `place-cong` carries an equation of the smaller width
-- there, and `lemma-5-1` an equality of semantics.  The rest identifies
-- a placed circuit with the spelling a derivation uses: placing is a
-- homomorphism (`place-•`), a circuit on the wires below i stays where
-- it is (`place-low`, the swap rules (f1)–(f4) as in TopWeakening, but
-- for a cycle of the bottom wires only), and one above i moves up a
-- wire (`place-high`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Place where

open import Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

import Presentation.Base as PB

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; Ex² ; ax)
open import Examples.Groups.Real-Clifford+CH.TopWeakening using (_↧ ; top)

private
  variable
    n r : ℕ

------------------------------------------------------------------------
-- Two facts about the bottom wires

-- A two-wire circuit at the bottom passes anything two wires up (as in
-- TopWeakening, where it is private).
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

-- Shifting k wires and then one more is shifting k + 1.
↑ᵏ-↑ : (v : Circuit n) (k : ℕ) → (v ↑ᵏ k) ↑ ≡ v ↑ᵏ (suc k)
↑ᵏ-↑ [ g ]ʷ  k = Eq.refl
↑ᵏ-↑ ε       k = Eq.refl
↑ᵏ-↑ (u • v) k = Eq.cong₂ _•_ (↑ᵏ-↑ u k) (↑ᵏ-↑ v k)

------------------------------------------------------------------------
-- The cycle of the bottom i + 1 wires

-- Wire 0 up to wire i, wires 1 … i each down one; and back.
cyc cyc⁻¹ : (i : ℕ) → Circuit (₁₊ (i +ℕ r))
cyc zero      = ε
cyc (suc i)   = Ex ↓ • cyc i ↑
cyc⁻¹ zero    = ε
cyc⁻¹ (suc i) = cyc⁻¹ i ↑ • Ex ↓

cyc-cyc⁻¹ : ∀ i → (₁₊ (i +ℕ r)) ⊢ cyc {r} i • cyc⁻¹ i ≈ ε
cyc-cyc⁻¹ zero = PB.left-unit
cyc-cyc⁻¹ {r} (suc i) = begin
  (Ex ↓ • cyc i ↑) • (cyc⁻¹ i ↑ • Ex ↓)   ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
  Ex ↓ • (cyc i ↑ • cyc⁻¹ i ↑) • Ex ↓     ≈⟨ back _ (front _ (lemma-cong↑ (cyc i • cyc⁻¹ i) ε (cyc-cyc⁻¹ i))) ⟩
  Ex ↓ • ε • Ex ↓                         ≈⟨ back _ left-unit ⟩
  Ex ↓ • Ex ↓                             ≈⟨ Ex² ⟩
  ε ∎
  where open Tools ((₂₊ (i +ℕ r)) VRel,_===_)

cyc⁻¹-cyc : ∀ i → (₁₊ (i +ℕ r)) ⊢ cyc⁻¹ {r} i • cyc i ≈ ε
cyc⁻¹-cyc zero = PB.left-unit
cyc⁻¹-cyc {r} (suc i) = begin
  (cyc⁻¹ i ↑ • Ex ↓) • (Ex ↓ • cyc i ↑)   ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
  cyc⁻¹ i ↑ • (Ex ↓ • Ex ↓) • cyc i ↑     ≈⟨ back _ (front _ Ex²) ⟩
  cyc⁻¹ i ↑ • ε • cyc i ↑                 ≈⟨ back _ left-unit ⟩
  cyc⁻¹ i ↑ • cyc i ↑                     ≈⟨ lemma-cong↑ (cyc⁻¹ i • cyc i) ε (cyc⁻¹-cyc i) ⟩
  ε ∎
  where open Tools ((₂₊ (i +ℕ r)) VRel,_===_)

------------------------------------------------------------------------
-- Naturality of the cycle for the wires below its top

-- One gate on the bottom i wires, one wire up, is carried back down.
lnat-gen : ∀ i (g : Gen i) → (₁₊ (i +ℕ r)) ⊢ [ g ↧ᵏ r ]ʷ ↑ • cyc i ≈ cyc i • [ g ↧ ↧ᵏ r ]ʷ
lnat-gen zero (gate₀ ())
lnat-gen (suc i) (gate₀ ())
lnat-gen {r} (suc i) (gate₁ h) = begin
  [ gate₁ h ]ʷ ↑ • Ex ↓ • cyc i ↑       ≈⟨ sym assoc ⟩
  ([ gate₁ h ]ʷ ↑ • Ex ↓) • cyc i ↑     ≈⟨ front _ (swap₁ h) ⟩
  (Ex ↓ • [ gate₁ h ]ʷ) • cyc i ↑       ≈⟨ assoc ⟩
  Ex ↓ • [ gate₁ h ]ʷ • cyc i ↑         ≈⟨ back _ (sym (comm-gate₁-w↑ h (cyc i))) ⟩
  Ex ↓ • cyc i ↑ • [ gate₁ h ]ʷ         ≈⟨ sym assoc ⟩
  (Ex ↓ • cyc i ↑) • [ gate₁ h ]ʷ ∎
  where
  open Tools ((₂₊ (i +ℕ r)) VRel,_===_)
  swap₁ : ∀ h → (₂₊ (i +ℕ r)) ⊢ [ gate₁ h ]ʷ ↑ • Ex ≈ Ex • [ gate₁ h ]ʷ
  swap₁ H-gate = ax swap-H
  swap₁ Z-gate = ax swap-Z
lnat-gen {r} (suc (suc i)) (gate₂ h) = begin
  [ gate₂ h ]ʷ ↑ • Ex ↓ • Ex ↑ • cyc i ↑ ↑
    ≈⟨ by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl ⟩
  ([ gate₂ h ]ʷ ↑ • Ex ↓ • Ex ↑) • cyc i ↑ ↑
    ≈⟨ front _ (swap₂ h) ⟩
  (Ex ↓ • Ex ↑ • [ gate₂ h ]ʷ) • cyc i ↑ ↑
    ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • (□ • □)) Eq.refl ⟩
  Ex ↓ • Ex ↑ • ([ gate₂ h ]ʷ • cyc i ↑ ↑)
    ≈⟨ back _ (back _ (sym (comm-gate₂-w↑↑ h (cyc i)))) ⟩
  Ex ↓ • Ex ↑ • (cyc i ↑ ↑ • [ gate₂ h ]ʷ)
    ≈⟨ by-passoc (□ • □ • (□ • □)) ((□ • □ • □) • □) Eq.refl ⟩
  (Ex ↓ • Ex ↑ • cyc i ↑ ↑) • [ gate₂ h ]ʷ ∎
  where
  open Tools ((₃₊ (i +ℕ r)) VRel,_===_)
  swap₂ : ∀ h → (₃₊ (i +ℕ r)) ⊢ [ gate₂ h ]ʷ ↑ • Ex ↓ • Ex ↑ ≈ Ex ↓ • Ex ↑ • [ gate₂ h ]ʷ
  swap₂ CZ-gate = ax swap-CZ
  swap₂ CH-gate = ax swap-CH
lnat-gen {r} (suc i) (g ↥) = begin
  [ g ↧ᵏ r ]ʷ ↑ ↑ • Ex ↓ • cyc i ↑           ≈⟨ sym assoc ⟩
  ([ g ↧ᵏ r ]ʷ ↑ ↑ • Ex ↓) • cyc i ↑         ≈⟨ front _ (sym (low-comm Ex [ g ↧ᵏ r ]ʷ)) ⟩
  (Ex ↓ • [ g ↧ᵏ r ]ʷ ↑ ↑) • cyc i ↑         ≈⟨ assoc ⟩
  Ex ↓ • [ g ↧ᵏ r ]ʷ ↑ ↑ • cyc i ↑           ≈⟨ back _ (lemma-cong↑ ([ g ↧ᵏ r ]ʷ ↑ • cyc i)
                                                    (cyc i • [ g ↧ ↧ᵏ r ]ʷ) (lnat-gen i g)) ⟩
  Ex ↓ • cyc i ↑ • [ g ↧ ↧ᵏ r ]ʷ ↑           ≈⟨ sym assoc ⟩
  (Ex ↓ • cyc i ↑) • [ g ↧ ↧ᵏ r ]ʷ ↑ ∎
  where open Tools ((₂₊ (i +ℕ r)) VRel,_===_)

-- A circuit on the bottom i wires.
lnat : ∀ i (c : Circuit i) → (₁₊ (i +ℕ r)) ⊢ (c ↓ᵏ r) ↑ • cyc i ≈ cyc i • (top c ↓ᵏ r)
lnat i [ g ]ʷ = lnat-gen i g
lnat {r} i ε = trans left-unit (sym right-unit)
  where open Tools ((₁₊ (i +ℕ r)) VRel,_===_)
lnat {r} i (w • v) = begin
  ((w ↓ᵏ r) ↑ • (v ↓ᵏ r) ↑) • cyc i         ≈⟨ assoc ⟩
  (w ↓ᵏ r) ↑ • ((v ↓ᵏ r) ↑ • cyc i)         ≈⟨ back _ (lnat i v) ⟩
  (w ↓ᵏ r) ↑ • (cyc i • (top v ↓ᵏ r))       ≈⟨ sym assoc ⟩
  ((w ↓ᵏ r) ↑ • cyc i) • (top v ↓ᵏ r)       ≈⟨ front _ (lnat i w) ⟩
  (cyc i • (top w ↓ᵏ r)) • (top v ↓ᵏ r)     ≈⟨ assoc ⟩
  cyc i • (top w ↓ᵏ r) • (top v ↓ᵏ r) ∎
  where open Tools ((₁₊ (i +ℕ r)) VRel,_===_)

------------------------------------------------------------------------
-- The cycle passes anything above its top

cyc-high-gen : ∀ i (g : Gen r) → (₁₊ (i +ℕ r)) ⊢ cyc i • [ g ↥ᵏ suc i ]ʷ ≈ [ g ↥ᵏ suc i ]ʷ • cyc i
cyc-high-gen {r} zero g = trans left-unit (sym right-unit)
  where open Tools ((₁₊ r) VRel,_===_)
cyc-high-gen {r} (suc i) g = begin
  (Ex ↓ • cyc i ↑) • [ g ↥ᵏ i ]ʷ ↑ ↑        ≈⟨ assoc ⟩
  Ex ↓ • cyc i ↑ • [ g ↥ᵏ i ]ʷ ↑ ↑          ≈⟨ back _ (lemma-cong↑ (cyc i • [ g ↥ᵏ suc i ]ʷ)
                                                  ([ g ↥ᵏ suc i ]ʷ • cyc i) (cyc-high-gen i g)) ⟩
  Ex ↓ • [ g ↥ᵏ i ]ʷ ↑ ↑ • cyc i ↑          ≈⟨ sym assoc ⟩
  (Ex ↓ • [ g ↥ᵏ i ]ʷ ↑ ↑) • cyc i ↑        ≈⟨ front _ (low-comm Ex [ g ↥ᵏ i ]ʷ) ⟩
  ([ g ↥ᵏ i ]ʷ ↑ ↑ • Ex ↓) • cyc i ↑        ≈⟨ assoc ⟩
  [ g ↥ᵏ i ]ʷ ↑ ↑ • Ex ↓ • cyc i ↑ ∎
  where open Tools ((₂₊ (i +ℕ r)) VRel,_===_)

cyc-high : ∀ i (v : Circuit r) → (₁₊ (i +ℕ r)) ⊢ cyc i • (v ↑ᵏ suc i) ≈ (v ↑ᵏ suc i) • cyc i
cyc-high i [ g ]ʷ = cyc-high-gen i g
cyc-high {r} i ε = trans right-unit (sym left-unit)
  where open Tools ((₁₊ (i +ℕ r)) VRel,_===_)
cyc-high {r} i (w • v) = begin
  cyc i • ((w ↑ᵏ suc i) • (v ↑ᵏ suc i))       ≈⟨ sym assoc ⟩
  (cyc i • (w ↑ᵏ suc i)) • (v ↑ᵏ suc i)       ≈⟨ front _ (cyc-high i w) ⟩
  ((w ↑ᵏ suc i) • cyc i) • (v ↑ᵏ suc i)       ≈⟨ assoc ⟩
  (w ↑ᵏ suc i) • (cyc i • (v ↑ᵏ suc i))       ≈⟨ back _ (cyc-high i v) ⟩
  (w ↑ᵏ suc i) • ((v ↑ᵏ suc i) • cyc i)       ≈⟨ sym assoc ⟩
  ((w ↑ᵏ suc i) • (v ↑ᵏ suc i)) • cyc i ∎
  where open Tools ((₁₊ (i +ℕ r)) VRel,_===_)

------------------------------------------------------------------------
-- Placing

place : (i : ℕ) → Circuit (i +ℕ r) → Circuit (₁₊ (i +ℕ r))
place i u = cyc⁻¹ i • u ↑ • cyc i

place-cong : ∀ i {u v : Circuit (i +ℕ r)} → (i +ℕ r) ⊢ u ≈ v →
             (₁₊ (i +ℕ r)) ⊢ place i u ≈ place i v
place-cong {r} i {u} {v} e = cong refl (cong (lemma-cong↑ u v e) refl)
  where open Tools ((₁₊ (i +ℕ r)) VRel,_===_)

-- Lemma 5.1: completeness one width down, on the wires other than i.
lemma-5-1 : ∀ i → (∀ {u v : Circuit (i +ℕ r)} → ⟦ u ⟧ ~ ⟦ v ⟧ → (i +ℕ r) ⊢ u ≈ v) →
            ∀ {u v : Circuit (i +ℕ r)} → ⟦ u ⟧ ~ ⟦ v ⟧ →
            (₁₊ (i +ℕ r)) ⊢ place i u ≈ place i v
lemma-5-1 i complete e = place-cong i (complete e)

place-• : ∀ i (u v : Circuit (i +ℕ r)) →
          (₁₊ (i +ℕ r)) ⊢ place i (u • v) ≈ place i u • place i v
place-• {r} i u v = begin
  cyc⁻¹ i • (u ↑ • v ↑) • cyc i
    ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • (□ • □)) Eq.refl ⟩
  (cyc⁻¹ i • u ↑) • (v ↑ • cyc i)
    ≈⟨ back _ (sym left-unit) ⟩
  (cyc⁻¹ i • u ↑) • (ε • v ↑ • cyc i)
    ≈⟨ back _ (front _ (sym (cyc-cyc⁻¹ i))) ⟩
  (cyc⁻¹ i • u ↑) • ((cyc i • cyc⁻¹ i) • v ↑ • cyc i)
    ≈⟨ by-passoc ((□ • □) • ((□ • □) • □ • □)) ((□ • □ • □) • (□ • □ • □)) Eq.refl ⟩
  (cyc⁻¹ i • u ↑ • cyc i) • (cyc⁻¹ i • v ↑ • cyc i) ∎
  where open Tools ((₁₊ (i +ℕ r)) VRel,_===_)

-- A circuit on the wires below i stays where it is.
place-low : ∀ i (c : Circuit i) → (₁₊ (i +ℕ r)) ⊢ place i (c ↓ᵏ r) ≈ top c ↓ᵏ r
place-low {r} i c = begin
  cyc⁻¹ i • (c ↓ᵏ r) ↑ • cyc i    ≈⟨ back _ (lnat i c) ⟩
  cyc⁻¹ i • cyc i • (top c ↓ᵏ r)  ≈⟨ sym assoc ⟩
  (cyc⁻¹ i • cyc i) • (top c ↓ᵏ r) ≈⟨ front _ (cyc⁻¹-cyc i) ⟩
  ε • (top c ↓ᵏ r)                ≈⟨ left-unit ⟩
  top c ↓ᵏ r ∎
  where open Tools ((₁₊ (i +ℕ r)) VRel,_===_)

-- One on the wires above i moves up a wire.
place-high : ∀ i (v : Circuit r) → (₁₊ (i +ℕ r)) ⊢ place i (v ↑ᵏ i) ≈ (v ↑ᵏ suc i)
place-high {r} i v = begin
  cyc⁻¹ i • (v ↑ᵏ i) ↑ • cyc i     ≈⟨ refl≡ (Eq.cong (λ w → cyc⁻¹ i • w • cyc i) (↑ᵏ-↑ v i)) ⟩
  cyc⁻¹ i • (v ↑ᵏ suc i) • cyc i     ≈⟨ back _ (sym (cyc-high i v)) ⟩
  cyc⁻¹ i • cyc i • (v ↑ᵏ suc i)     ≈⟨ sym assoc ⟩
  (cyc⁻¹ i • cyc i) • (v ↑ᵏ suc i)   ≈⟨ front _ (cyc⁻¹-cyc i) ⟩
  ε • (v ↑ᵏ suc i)                   ≈⟨ left-unit ⟩
  (v ↑ᵏ suc i) ∎
  where
  open Tools ((₁₊ (i +ℕ r)) VRel,_===_)
  refl≡ : ∀ {a b : Circuit (₁₊ (i +ℕ r))} → a ≡ b → (₁₊ (i +ℕ r)) ⊢ a ≈ b
  refl≡ Eq.refl = refl
