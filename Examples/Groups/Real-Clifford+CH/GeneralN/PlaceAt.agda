------------------------------------------------------------------------
-- Presentations of groups
--
-- Placing a circuit around an idle wire given by its number
--
-- Place.place i fixes the width as i + r, which a wire number read off
-- a layout (MultiControlled) does not provide.  Here the width is
-- implicit and the wire a number, in MultiControlled's style (Xat,
-- swapAt): the cycle of the wires 0 … c, `cycAt c`, is the identity when
-- there is no wire c, and `placeAt c u` puts u on the wires other than
-- c.  `placeAt-place` identifies it with Place.place where both are
-- defined.  Moving the idle wire up is conjugating by a swap
-- (`placeAt-step`), because the cycles differ by that swap on the side
-- of the idle wire (`cycAt-step`, `cycAt⁻¹-step`); and X moves by the
-- same swaps (`X-step`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt where

open import Data.Nat using (ℕ ; zero ; suc ; _<_ ; s≤s ; z≤n) renaming (_+_ to _+ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; Ex² ; ax)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (Xat ; swapAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (cyc ; cyc⁻¹ ; place)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑ ; swapX ; swapX′)

private
  variable
    n r : ℕ

------------------------------------------------------------------------
-- The cycles and the placement

-- Split on the wire first, so that cycAt 0 is ε at any width.
mutual
  cycAt cycAt⁻¹ : ℕ → Circuit n
  cycAt zero    = ε
  cycAt (suc c) = cycS c
  cycAt⁻¹ zero    = ε
  cycAt⁻¹ (suc c) = cycS⁻¹ c

  cycS cycS⁻¹ : ℕ → Circuit n
  cycS {₂₊ n} c = Ex ↓ • cycAt c ↑
  cycS        c = ε
  cycS⁻¹ {₂₊ n} c = cycAt⁻¹ c ↑ • Ex ↓
  cycS⁻¹        c = ε

placeAt : ℕ → Circuit n → Circuit (₁₊ n)
placeAt c u = cycAt⁻¹ c • u ↑ • cycAt c

-- Where both are defined, the same as Place's.
cycAt≡ : ∀ i → cycAt {₁₊ (i +ℕ r)} i ≡ cyc {r} i
cycAt≡ zero    = Eq.refl
cycAt≡ (suc i) = Eq.cong (λ w → Ex ↓ • w ↑) (cycAt≡ i)

cycAt⁻¹≡ : ∀ i → cycAt⁻¹ {₁₊ (i +ℕ r)} i ≡ cyc⁻¹ {r} i
cycAt⁻¹≡ zero    = Eq.refl
cycAt⁻¹≡ (suc i) = Eq.cong (λ w → w ↑ • Ex ↓) (cycAt⁻¹≡ i)

placeAt-place : ∀ i (u : Circuit (i +ℕ r)) → placeAt i u ≡ place i u
placeAt-place i u = Eq.cong₂ (λ a b → a • u ↑ • b) (cycAt⁻¹≡ i) (cycAt≡ i)

------------------------------------------------------------------------
-- One wire further up is one swap more

cycAt⁻¹-step : ∀ c → c < n → (₁₊ n) ⊢ cycAt⁻¹ (suc c) ≈ swapAt c • cycAt⁻¹ c
cycAt⁻¹-step {zero}  c ()
cycAt⁻¹-step {suc n} zero (s≤s z≤n) = trans left-unit (sym right-unit)
  where open Tools ((₂₊ n) VRel,_===_)
cycAt⁻¹-step {suc n} (suc c) (s≤s c<n) = begin
  cycAt⁻¹ (suc c) ↑ • Ex ↓
    ≈⟨ front _ (lemma-cong↑ (cycAt⁻¹ (suc c)) (swapAt c • cycAt⁻¹ c) (cycAt⁻¹-step c c<n)) ⟩
  (swapAt c ↑ • cycAt⁻¹ c ↑) • Ex ↓
    ≈⟨ assoc ⟩
  swapAt c ↑ • (cycAt⁻¹ c ↑ • Ex ↓) ∎
  where open Tools ((₂₊ n) VRel,_===_)

cycAt-step : ∀ c → c < n → (₁₊ n) ⊢ cycAt (suc c) ≈ cycAt c • swapAt c
cycAt-step {zero}  c ()
cycAt-step {suc n} zero (s≤s z≤n) = trans right-unit (sym left-unit)
  where open Tools ((₂₊ n) VRel,_===_)
cycAt-step {suc n} (suc c) (s≤s c<n) = begin
  Ex ↓ • cycAt (suc c) ↑
    ≈⟨ back _ (lemma-cong↑ (cycAt (suc c)) (cycAt c • swapAt c) (cycAt-step c c<n)) ⟩
  Ex ↓ • (cycAt c ↑ • swapAt c ↑)
    ≈⟨ sym assoc ⟩
  (Ex ↓ • cycAt c ↑) • swapAt c ↑ ∎
  where open Tools ((₂₊ n) VRel,_===_)

placeAt-step : ∀ c (u : Circuit n) → c < n →
               (₁₊ n) ⊢ placeAt (suc c) u ≈ swapAt c • placeAt c u • swapAt c
placeAt-step {n} c u c<n = begin
  cycAt⁻¹ (suc c) • u ↑ • cycAt (suc c)
    ≈⟨ cong (cycAt⁻¹-step c c<n) (back _ (cycAt-step c c<n)) ⟩
  (swapAt c • cycAt⁻¹ c) • u ↑ • (cycAt c • swapAt c)
    ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
  swapAt c • (cycAt⁻¹ c • u ↑ • cycAt c) • swapAt c ∎
  where open Tools ((₁₊ n) VRel,_===_)

------------------------------------------------------------------------
-- X along the swaps

private
  -- X one wire up is X conjugated by the swap.
  Ex-X-Ex : (₂₊ n) ⊢ Ex ↓ • X ↓ • Ex ↓ ≈ X ↑
  Ex-X-Ex {n} = sym (begin
    X ↑                  ≈⟨ sym (trans assoc (trans (back _ Ex²) right-unit)) ⟩
    (X ↑ • Ex ↓) • Ex ↓  ≈⟨ front _ swapX ⟩
    (Ex ↓ • X ↓) • Ex ↓  ≈⟨ assoc ⟩
    Ex ↓ • X ↓ • Ex ↓ ∎)
    where open Tools ((₂₊ n) VRel,_===_)

X-step : ∀ c → c < n → (₁₊ n) ⊢ swapAt c • Xat c • swapAt c ≈ Xat (suc c)
X-step {zero}  c ()
X-step {suc n} zero    (s≤s z≤n) = Ex-X-Ex
X-step {suc n} (suc c) (s≤s c<n) =
  lemma-cong↑ (swapAt c • Xat c • swapAt c) (Xat (suc c)) (X-step c c<n)

-- X on the idle wire passes the placed circuit.
X-cycAt⁻¹ : ∀ c → c < ₁₊ n → (₁₊ n) ⊢ Xat c • cycAt⁻¹ c ≈ cycAt⁻¹ c • X
X-cycAt⁻¹ {n} zero _ = trans right-unit (sym left-unit)
  where open Tools ((₁₊ n) VRel,_===_)
X-cycAt⁻¹ {zero}  (suc c) (s≤s ())
X-cycAt⁻¹ {suc n} (suc c) (s≤s c<n) = begin
  Xat c ↑ • (cycAt⁻¹ c ↑ • Ex ↓)
    ≈⟨ sym assoc ⟩
  (Xat c ↑ • cycAt⁻¹ c ↑) • Ex ↓
    ≈⟨ front _ (lemma-cong↑ (Xat c • cycAt⁻¹ c) (cycAt⁻¹ c • X) (X-cycAt⁻¹ c c<n)) ⟩
  (cycAt⁻¹ c ↑ • X ↑) • Ex ↓
    ≈⟨ assoc ⟩
  cycAt⁻¹ c ↑ • (X ↑ • Ex ↓)
    ≈⟨ back _ swapX ⟩
  cycAt⁻¹ c ↑ • (Ex ↓ • X ↓)
    ≈⟨ sym assoc ⟩
  (cycAt⁻¹ c ↑ • Ex ↓) • X ∎
  where open Tools ((₂₊ n) VRel,_===_)

cycAt-X : ∀ c → c < ₁₊ n → (₁₊ n) ⊢ cycAt c • Xat c ≈ X • cycAt c
cycAt-X {n} zero _ = trans left-unit (sym right-unit)
  where open Tools ((₁₊ n) VRel,_===_)
cycAt-X {zero}  (suc c) (s≤s ())
cycAt-X {suc n} (suc c) (s≤s c<n) = begin
  (Ex ↓ • cycAt c ↑) • Xat c ↑
    ≈⟨ assoc ⟩
  Ex ↓ • (cycAt c ↑ • Xat c ↑)
    ≈⟨ back _ (lemma-cong↑ (cycAt c • Xat c) (X • cycAt c) (cycAt-X c c<n)) ⟩
  Ex ↓ • (X ↑ • cycAt c ↑)
    ≈⟨ sym assoc ⟩
  (Ex ↓ • X ↑) • cycAt c ↑
    ≈⟨ front _ swapX′ ⟩
  (X ↓ • Ex ↓) • cycAt c ↑
    ≈⟨ assoc ⟩
  X • (Ex ↓ • cycAt c ↑) ∎
  where open Tools ((₂₊ n) VRel,_===_)

X-placeAt : ∀ c (u : Circuit n) → c < ₁₊ n → (₁₊ n) ⊢ Xat c • placeAt c u ≈ placeAt c u • Xat c
X-placeAt {n} c u c≤n = begin
  Xat c • (cycAt⁻¹ c • u ↑ • cycAt c)   ≈⟨ sym assoc ⟩
  (Xat c • cycAt⁻¹ c) • u ↑ • cycAt c   ≈⟨ front _ (X-cycAt⁻¹ c c≤n) ⟩
  (cycAt⁻¹ c • X) • u ↑ • cycAt c      ≈⟨ trans assoc (back _ (trans (sym assoc) (front _ (X-↑ u)))) ⟩
  cycAt⁻¹ c • (u ↑ • X) • cycAt c      ≈⟨ back _ (trans assoc (back _ (sym (cycAt-X c c≤n)))) ⟩
  cycAt⁻¹ c • u ↑ • (cycAt c • Xat c)   ≈⟨ by-passoc (□ • □ • (□ • □)) ((□ • □ • □) • □) Eq.refl ⟩
  (cycAt⁻¹ c • u ↑ • cycAt c) • Xat c ∎
  where open Tools ((₁₊ n) VRel,_===_)
