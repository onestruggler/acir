------------------------------------------------------------------------
-- Presentations of groups
--
-- Placing around an idle wire, and X on a wire
--
-- `placeAt c u` inserts an idle wire at c.  It is a homomorphism
-- (`placeAt-•`, `placeAt-ε`, `placeAt-cong`), since its two cycles are
-- inverse networks (SwapCalc).  X on a wire below c stays where it is
-- (`placeAt-X-lo`), X on a wire at c or above moves up one
-- (`placeAt-X-hi`) — both by moving the idle wire up one swap at a
-- time (`placeAt-step`), X passing every swap it does not touch
-- (`X-swap-lo`, `X-swap-hi`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.PlaceCalc where

open import Data.Nat using (ℕ ; zero ; suc ; _<_ ; _≤_ ; s≤s ; z≤n)
open import Data.Nat.Properties using (m<1+n⇒m<n∨m≡n ; ≤-refl ; ≤-trans ; n≤1+n)
open import Data.Sum using (inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; Ex²)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (Xat ; swapAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (low-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (cycAt ; cycAt⁻¹ ; placeAt ; placeAt-step ; X-step)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SwapCalc
  using (swapAt² ; sd-su ; su-sd ; cycAt⁻¹≈sd ; cycAt≈su)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- A homomorphism

module _ {n : ℕ} where
  open Tools ((₁₊ n) VRel,_===_)

  cyc-inv : ∀ c → cycAt {₁₊ n} c • cycAt⁻¹ c ≈ ε
  cyc-inv c = trans (cong (cycAt≈su c) (cycAt⁻¹≈sd c)) (su-sd c)

  cyc-inv′ : ∀ c → cycAt⁻¹ {₁₊ n} c • cycAt c ≈ ε
  cyc-inv′ c = trans (cong (cycAt⁻¹≈sd c) (cycAt≈su c)) (sd-su c)

  placeAt-• : ∀ c (a b : Circuit n) → placeAt c (a • b) ≈ placeAt c a • placeAt c b
  placeAt-• c a b = sym (begin
    (cycAt⁻¹ c • a ↑ • cycAt c) • (cycAt⁻¹ c • b ↑ • cycAt c)
      ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • ((□ • □) • □ • □)) Eq.refl ⟩
    cycAt⁻¹ c • a ↑ • ((cycAt c • cycAt⁻¹ c) • b ↑ • cycAt c)
      ≈⟨ back _ (back _ (trans (front _ (cyc-inv c)) left-unit)) ⟩
    cycAt⁻¹ c • a ↑ • (b ↑ • cycAt c)
      ≈⟨ back _ (sym assoc) ⟩
    cycAt⁻¹ c • (a ↑ • b ↑) • cycAt c ∎)

  placeAt-ε : ∀ c → placeAt {n} c ε ≈ ε
  placeAt-ε c = trans (back _ left-unit) (cyc-inv′ c)

  placeAt-cong : ∀ c {a b : Circuit n} → n ⊢ a ≈ b → placeAt c a ≈ placeAt c b
  placeAt-cong c {a} {b} e = back _ (front _ (lemma-cong↑ a b e))

------------------------------------------------------------------------
-- X and the swaps it does not touch

X-swap-lo : ∀ i c → i < c → n ⊢ Xat i • swapAt c ≈ swapAt c • Xat i
X-swap-lo {zero}        i       c       _ = refl
  where open Tools (zero VRel,_===_)
X-swap-lo {suc n}       i       zero    ()
X-swap-lo {suc zero}    zero    (suc c) _ = trans right-unit (sym left-unit)
  where open Tools ((₁₊ zero) VRel,_===_)
X-swap-lo {suc (suc n)} zero    (suc c) _ = X-↑ (swapAt c)
X-swap-lo {suc zero}    (suc i) (suc c) _ = refl
  where open Tools ((₁₊ zero) VRel,_===_)
X-swap-lo {suc (suc n)} (suc i) (suc c) (s≤s p) =
  lemma-cong↑ (Xat i • swapAt c) (swapAt c • Xat i) (X-swap-lo {suc n} i c p)

X-swap-hi : ∀ i c → ₂₊ c ≤ i → n ⊢ Xat i • swapAt c ≈ swapAt c • Xat i
X-swap-hi {zero}              i             c       _ = refl
  where open Tools (zero VRel,_===_)
X-swap-hi {suc n}             zero          c       ()
X-swap-hi {suc n}             (suc zero)    zero    (s≤s ())
X-swap-hi {suc zero}          (suc (suc i)) zero    _ = refl
  where open Tools ((₁₊ zero) VRel,_===_)
X-swap-hi {suc (suc n)}       (suc (suc i)) zero    _ = sym (low-comm Ex (Xat i))
  where open Tools ((₂₊ n) VRel,_===_)
X-swap-hi {suc zero}          (suc i)       (suc c) _ = refl
  where open Tools ((₁₊ zero) VRel,_===_)
X-swap-hi {suc (suc n)}       (suc i)       (suc c) (s≤s p) =
  lemma-cong↑ (Xat i • swapAt c) (swapAt c • Xat i) (X-swap-hi {suc n} i c p)

------------------------------------------------------------------------
-- X under placeAt

private
  -- A swap passing X, conjugated away.
  unconj-swap : ∀ c {a} → (₁₊ n) ⊢ a • swapAt c ≈ swapAt c • a → (₁₊ n) ⊢ swapAt c • a • swapAt c ≈ a
  unconj-swap {n} c {a} e = begin
    swapAt c • a • swapAt c     ≈⟨ back _ e ⟩
    swapAt c • swapAt c • a     ≈⟨ trans (sym assoc) (trans (front _ (swapAt² c)) left-unit) ⟩
    a ∎
    where open Tools ((₁₊ n) VRel,_===_)

  -- X-step backwards.
  X-step′ : ∀ c → c < n → (₁₊ n) ⊢ swapAt c • Xat (suc c) • swapAt c ≈ Xat c
  X-step′ {n} c c<n = begin
    swapAt c • Xat (suc c) • swapAt c                         ≈⟨ back _ (front _ (sym (X-step c c<n))) ⟩
    swapAt c • (swapAt c • Xat c • swapAt c) • swapAt c       ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
    (swapAt c • swapAt c) • Xat c • (swapAt c • swapAt c)     ≈⟨ cong (swapAt² c) (back _ (swapAt² c)) ⟩
    ε • Xat c • ε                                             ≈⟨ trans left-unit right-unit ⟩
    Xat c ∎
    where open Tools ((₁₊ n) VRel,_===_)

placeAt-X-lo : ∀ c i → i < c → c ≤ n → (₁₊ n) ⊢ placeAt {n} c (Xat i) ≈ Xat i
placeAt-X-hi : ∀ c i → c ≤ i → c ≤ n → (₁₊ n) ⊢ placeAt {n} c (Xat i) ≈ Xat (suc i)

placeAt-X-lo zero    i () _
placeAt-X-lo {n} (suc c) i i<c c<n with m<1+n⇒m<n∨m≡n i<c
... | inj₁ i<c′ = begin
  placeAt (suc c) (Xat i)                   ≈⟨ placeAt-step c (Xat i) c<n ⟩
  swapAt c • placeAt c (Xat i) • swapAt c   ≈⟨ back _ (front _ (placeAt-X-lo c i i<c′ (≤-trans (n≤1+n c) c<n))) ⟩
  swapAt c • Xat i • swapAt c               ≈⟨ unconj-swap c (X-swap-lo i c i<c′) ⟩
  Xat i ∎
  where open Tools ((₁₊ n) VRel,_===_)
... | inj₂ Eq.refl = begin
  placeAt (suc c) (Xat c)                   ≈⟨ placeAt-step c (Xat c) c<n ⟩
  swapAt c • placeAt c (Xat c) • swapAt c   ≈⟨ back _ (front _ (placeAt-X-hi c c ≤-refl (≤-trans (n≤1+n c) c<n))) ⟩
  swapAt c • Xat (suc c) • swapAt c         ≈⟨ X-step′ c c<n ⟩
  Xat c ∎
  where open Tools ((₁₊ n) VRel,_===_)

placeAt-X-hi {n} zero    i _ _ = trans left-unit right-unit
  where open Tools ((₁₊ n) VRel,_===_)
placeAt-X-hi {n} (suc c) i c<i c<n = begin
  placeAt (suc c) (Xat i)                   ≈⟨ placeAt-step c (Xat i) c<n ⟩
  swapAt c • placeAt c (Xat i) • swapAt c   ≈⟨ back _ (front _ (placeAt-X-hi c i (≤-trans (n≤1+n c) c<i) (≤-trans (n≤1+n c) c<n))) ⟩
  swapAt c • Xat (suc i) • swapAt c         ≈⟨ unconj-swap c (X-swap-hi (suc i) c (s≤s c<i)) ⟩
  Xat (suc i) ∎
  where open Tools ((₁₊ n) VRel,_===_)

------------------------------------------------------------------------
-- Inserting at 0, and one wire up

placeAt-zero : ∀ (u : Circuit n) → (₁₊ n) ⊢ placeAt 0 u ≈ u ↑
placeAt-zero {n} u = trans left-unit right-unit
  where open Tools ((₁₊ n) VRel,_===_)

placeAt-↑ : ∀ c (u : Circuit n) → (₂₊ n) ⊢ placeAt (suc c) (u ↑) ≈ (placeAt c u) ↑
placeAt-↑ {n} c u = begin
  (cycAt⁻¹ c ↑ • Ex ↓) • u ↑ ↑ • (Ex ↓ • cycAt c ↑)
    ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
  cycAt⁻¹ c ↑ • (Ex • u ↑ ↑ • Ex) • cycAt c ↑
    ≈⟨ back _ (front _ (trans (sym assoc) (trans (front _ (low-comm Ex u)) (trans assoc (trans (back _ Ex²) right-unit))))) ⟩
  cycAt⁻¹ c ↑ • u ↑ ↑ • cycAt c ↑ ∎
  where open Tools ((₂₊ n) VRel,_===_)
