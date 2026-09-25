------------------------------------------------------------------------
-- Presentations of groups
--
-- Swaps by wire number, and the networks of MultiControlled
--
-- MultiControlled places a gate by `shiftDown t` (wire t down to wire
-- 0, the wires below it each up one) and `shiftUp t`, products of the
-- swaps `swapAt i` of the wires i, i + 1.  Here, at any width and any
-- wire numbers: a swap is an involution (`swapAt²`), swaps two or more
-- wires apart commute (`swap-far`), the braid relation (`swap-braid`),
-- and a swap passes `shiftDown t` renumbered: unchanged above t
-- (`sd-above`), one up below it (`sd-below`); likewise `shiftUp`
-- (`su-above`, `su-below`), the two networks being inverse (`sd-su`,
-- `su-sd`).  And PlaceAt's cycles are these networks (`cycAt⁻¹≈sd`,
-- `cycAt≈su`), so `placeAt c u` is `shiftDown c • u ↑ • shiftUp c`.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.SwapCalc where

open import Data.Nat using (ℕ ; zero ; suc ; _<_ ; s≤s ; z≤n) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (m≤n+m ; <-trans ; n<1+n)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; Ex²)
open import Examples.Groups.Real-Clifford+CH.TopWeakening using (nat)
open import Examples.Groups.Real-Clifford+CH.Weakening using (weaken)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (swapAt ; shiftDown ; shiftUp)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (low-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (cycAt ; cycAt⁻¹ ; placeAt)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Swaps

-- `swapAt {₁₊ n} (suc i)` is stuck at a symbolic n (swapAt splits on
-- the width twice before the wire), so every clause below that needs
-- it to reduce names the width ₂₊ n.

swapAt² : ∀ c → n ⊢ swapAt c • swapAt c ≈ ε
swapAt² {zero}        c       = left-unit
  where open Tools (zero VRel,_===_)
swapAt² {suc zero}    zero    = left-unit
  where open Tools (₁₊ zero VRel,_===_)
swapAt² {suc zero}    (suc c) = left-unit
  where open Tools (₁₊ zero VRel,_===_)
swapAt² {suc (suc n)} zero    = Ex²
swapAt² {suc (suc n)} (suc c) = lemma-cong↑ (swapAt c • swapAt c) ε (swapAt² {suc n} c)

swap-far : ∀ i j → suc i < j → n ⊢ swapAt i • swapAt j ≈ swapAt j • swapAt i
swap-far {zero}              i       j             _ = refl
  where open Tools (zero VRel,_===_)
swap-far {suc n}             i       zero          ()
swap-far {suc n}             zero    (suc zero)    (s≤s ())
swap-far {suc n}             (suc i) (suc zero)    (s≤s ())
swap-far {suc zero}          zero    (suc (suc j)) _ = refl
  where open Tools (₁₊ zero VRel,_===_)
swap-far {suc (suc zero)}    zero    (suc (suc j)) _ = trans right-unit (sym left-unit)
  where open Tools (₂₊ zero VRel,_===_)
swap-far {suc (suc (suc n))} zero    (suc (suc j)) _ = low-comm Ex (swapAt j)
swap-far {suc zero}          (suc i) (suc (suc j)) _ = refl
  where open Tools (₁₊ zero VRel,_===_)
swap-far {suc (suc n)}       (suc i) (suc (suc j)) (s≤s b) =
  lemma-cong↑ (swapAt i • swapAt (suc j)) (swapAt (suc j) • swapAt i) (swap-far {suc n} i (suc j) b)

swap-braid : ∀ i → ₂₊ i < n →
             n ⊢ swapAt i • swapAt (suc i) • swapAt i ≈ swapAt (suc i) • swapAt i • swapAt (suc i)
swap-braid {zero}              zero    ()
swap-braid {suc zero}          zero    (s≤s ())
swap-braid {suc (suc zero)}    zero    (s≤s (s≤s ()))
swap-braid {suc (suc (suc n))} zero    _ = begin
  Ex • Ex ↑ • Ex                    ≈⟨ by-passoc (□ • □ • □) ((□ • (□ • ε)) • □) Eq.refl ⟩
  (Ex • (Ex ↑ • ε)) • Ex            ≈⟨ sym (weaken n (s≤s (s≤s (s≤s z≤n))) (nat {2} Ex)) ⟩
  Ex ↑ • (Ex • (Ex ↑ • ε))          ≈⟨ by-passoc (□ • (□ • (□ • ε))) (□ • □ • □) Eq.refl ⟩
  Ex ↑ • Ex • Ex ↑ ∎
  where open Tools ((₃₊ n) VRel,_===_)
swap-braid {zero}              (suc i) ()
swap-braid {suc zero}          (suc i) (s≤s ())
swap-braid {suc (suc n)}       (suc i) (s≤s b) =
  lemma-cong↑ (swapAt i • swapAt (suc i) • swapAt i) (swapAt (suc i) • swapAt i • swapAt (suc i))
              (swap-braid {suc n} i b)

------------------------------------------------------------------------
-- A swap past shiftDown and shiftUp

sd-above : ∀ t i → t < i → n ⊢ swapAt i • shiftDown t ≈ shiftDown t • swapAt i
sd-above {n} zero    i _ = trans right-unit (sym left-unit)
  where open Tools (n VRel,_===_)
sd-above {n} (suc t) i b = begin
  swapAt i • (swapAt t • shiftDown t)     ≈⟨ sym assoc ⟩
  (swapAt i • swapAt t) • shiftDown t     ≈⟨ front _ (sym (swap-far t i b)) ⟩
  (swapAt t • swapAt i) • shiftDown t     ≈⟨ assoc ⟩
  swapAt t • (swapAt i • shiftDown t)     ≈⟨ back _ (sd-above t i (<-trans (n<1+n t) b)) ⟩
  swapAt t • (shiftDown t • swapAt i)     ≈⟨ sym assoc ⟩
  (swapAt t • shiftDown t) • swapAt i ∎
  where open Tools (n VRel,_===_)

-- Below the target, the swap comes out one wire up: the target at
-- t = 2 + d + i above the swap of the wires i, i + 1.
sd-below : ∀ i d → ₂₊ (d +ℕ i) < n →
           n ⊢ swapAt i • shiftDown (₂₊ (d +ℕ i)) ≈ shiftDown (₂₊ (d +ℕ i)) • swapAt (suc i)
sd-below {n} i zero b = begin
  swapAt i • (swapAt (suc i) • (swapAt i • shiftDown i))
    ≈⟨ by-passoc (□ • (□ • (□ • □))) ((□ • □ • □) • □) Eq.refl ⟩
  (swapAt i • swapAt (suc i) • swapAt i) • shiftDown i
    ≈⟨ front _ (swap-braid i b) ⟩
  (swapAt (suc i) • swapAt i • swapAt (suc i)) • shiftDown i
    ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • (□ • □)) Eq.refl ⟩
  swapAt (suc i) • swapAt i • (swapAt (suc i) • shiftDown i)
    ≈⟨ back _ (back _ (sd-above i (suc i) (n<1+n i))) ⟩
  swapAt (suc i) • swapAt i • (shiftDown i • swapAt (suc i))
    ≈⟨ by-passoc (□ • □ • (□ • □)) ((□ • (□ • □)) • □) Eq.refl ⟩
  (swapAt (suc i) • (swapAt i • shiftDown i)) • swapAt (suc i) ∎
  where open Tools (n VRel,_===_)
sd-below {n} i (suc d) b = begin
  swapAt i • (swapAt (₂₊ (d +ℕ i)) • shiftDown (₂₊ (d +ℕ i)))
    ≈⟨ sym assoc ⟩
  (swapAt i • swapAt (₂₊ (d +ℕ i))) • shiftDown (₂₊ (d +ℕ i))
    ≈⟨ front _ (swap-far i (₂₊ (d +ℕ i)) (s≤s (s≤s (m≤n+m i d)))) ⟩
  (swapAt (₂₊ (d +ℕ i)) • swapAt i) • shiftDown (₂₊ (d +ℕ i))
    ≈⟨ assoc ⟩
  swapAt (₂₊ (d +ℕ i)) • (swapAt i • shiftDown (₂₊ (d +ℕ i)))
    ≈⟨ back _ (sd-below i d (<-trans (n<1+n (₂₊ (d +ℕ i))) b)) ⟩
  swapAt (₂₊ (d +ℕ i)) • (shiftDown (₂₊ (d +ℕ i)) • swapAt (suc i))
    ≈⟨ sym assoc ⟩
  (swapAt (₂₊ (d +ℕ i)) • shiftDown (₂₊ (d +ℕ i))) • swapAt (suc i) ∎
  where open Tools (n VRel,_===_)

-- The two networks are inverse.
sd-su : ∀ t → n ⊢ shiftDown t • shiftUp t ≈ ε
sd-su {n} zero    = left-unit
  where open Tools (n VRel,_===_)
sd-su {n} (suc t) = begin
  (swapAt t • shiftDown t) • (shiftUp t • swapAt t)
    ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
  swapAt t • (shiftDown t • shiftUp t) • swapAt t
    ≈⟨ back _ (trans (front _ (sd-su t)) left-unit) ⟩
  swapAt t • swapAt t
    ≈⟨ swapAt² t ⟩
  ε ∎
  where open Tools (n VRel,_===_)

su-sd : ∀ t → n ⊢ shiftUp t • shiftDown t ≈ ε
su-sd {n} zero    = left-unit
  where open Tools (n VRel,_===_)
su-sd {n} (suc t) = begin
  (shiftUp t • swapAt t) • (swapAt t • shiftDown t)
    ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
  shiftUp t • (swapAt t • swapAt t) • shiftDown t
    ≈⟨ back _ (trans (front _ (swapAt² t)) left-unit) ⟩
  shiftUp t • shiftDown t
    ≈⟨ su-sd t ⟩
  ε ∎
  where open Tools (n VRel,_===_)

-- The same for shiftUp, by inverting.
private
  invert : ∀ {D U a b : Circuit n} → n ⊢ D • U ≈ ε → n ⊢ U • D ≈ ε →
           n ⊢ a • D ≈ D • b → n ⊢ U • a ≈ b • U
  invert {n} {D} {U} {a} {b} DU UD e = begin
    U • a                   ≈⟨ sym right-unit ⟩
    (U • a) • ε             ≈⟨ back _ (sym DU) ⟩
    (U • a) • (D • U)       ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
    U • (a • D) • U         ≈⟨ back _ (front _ e) ⟩
    U • (D • b) • U         ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
    (U • D) • b • U         ≈⟨ trans (front _ UD) left-unit ⟩
    b • U ∎
    where open Tools (n VRel,_===_)

su-above : ∀ t i → t < i → n ⊢ shiftUp t • swapAt i ≈ swapAt i • shiftUp t
su-above t i b = invert (sd-su t) (su-sd t) (sd-above t i b)

su-below : ∀ i d → ₂₊ (d +ℕ i) < n →
           n ⊢ shiftUp (₂₊ (d +ℕ i)) • swapAt i ≈ swapAt (suc i) • shiftUp (₂₊ (d +ℕ i))
su-below i d b = invert (sd-su (₂₊ (d +ℕ i))) (su-sd (₂₊ (d +ℕ i))) (sd-below i d b)

------------------------------------------------------------------------
-- PlaceAt's cycles are these networks

private
  -- On fewer than two wires there is nothing to swap.
  swap-ε : n < 2 → ∀ c → n ⊢ swapAt c ≈ ε
  swap-ε {zero}        _ c       = refl
    where open Tools (zero VRel,_===_)
  swap-ε {suc zero}    _ zero    = refl
    where open Tools (₁₊ zero VRel,_===_)
  swap-ε {suc zero}    _ (suc c) = refl
    where open Tools (₁₊ zero VRel,_===_)
  swap-ε {suc (suc n)} (s≤s (s≤s ())) c

  sd-ε : n < 2 → ∀ c → n ⊢ shiftDown c ≈ ε
  sd-ε {n} b zero    = refl
    where open Tools (n VRel,_===_)
  sd-ε {n} b (suc c) = trans (cong (swap-ε b c) (sd-ε b c)) left-unit
    where open Tools (n VRel,_===_)

  su-ε : n < 2 → ∀ c → n ⊢ shiftUp c ≈ ε
  su-ε {n} b zero    = refl
    where open Tools (n VRel,_===_)
  su-ε {n} b (suc c) = trans (cong (su-ε b c) (swap-ε b c)) left-unit
    where open Tools (n VRel,_===_)

  sd-↑ : ∀ c → (₂₊ n) ⊢ shiftDown c ↑ • Ex ↓ ≈ shiftDown (suc c)
  sd-↑ {n} zero    = trans left-unit (sym right-unit)
    where open Tools ((₂₊ n) VRel,_===_)
  sd-↑ {n} (suc c) = begin
    (swapAt c • shiftDown c) ↑ • Ex ↓       ≈⟨ assoc ⟩
    swapAt c ↑ • (shiftDown c ↑ • Ex ↓)     ≈⟨ back _ (sd-↑ c) ⟩
    swapAt c ↑ • shiftDown (suc c) ∎
    where open Tools ((₂₊ n) VRel,_===_)

  su-↑ : ∀ c → (₂₊ n) ⊢ Ex ↓ • shiftUp c ↑ ≈ shiftUp (suc c)
  su-↑ {n} zero    = trans right-unit (sym left-unit)
    where open Tools ((₂₊ n) VRel,_===_)
  su-↑ {n} (suc c) = begin
    Ex ↓ • (shiftUp c • swapAt c) ↑         ≈⟨ sym assoc ⟩
    (Ex ↓ • shiftUp c ↑) • swapAt c ↑       ≈⟨ front _ (su-↑ c) ⟩
    shiftUp (suc c) • swapAt c ↑ ∎
    where open Tools ((₂₊ n) VRel,_===_)

cycAt⁻¹≈sd : ∀ c → n ⊢ cycAt⁻¹ c ≈ shiftDown c
cycAt⁻¹≈sd {n}           zero    = refl
  where open Tools (n VRel,_===_)
cycAt⁻¹≈sd {zero}        (suc c) = sym (sd-ε (s≤s z≤n) (suc c))
  where open Tools (zero VRel,_===_)
cycAt⁻¹≈sd {suc zero}    (suc c) = sym (sd-ε (s≤s (s≤s z≤n)) (suc c))
  where open Tools (₁₊ zero VRel,_===_)
cycAt⁻¹≈sd {suc (suc n)} (suc c) =
  trans (cong (lemma-cong↑ (cycAt⁻¹ c) (shiftDown c) (cycAt⁻¹≈sd c)) refl) (sd-↑ c)
  where open Tools ((₂₊ n) VRel,_===_)

cycAt≈su : ∀ c → n ⊢ cycAt c ≈ shiftUp c
cycAt≈su {n}           zero    = refl
  where open Tools (n VRel,_===_)
cycAt≈su {zero}        (suc c) = sym (su-ε (s≤s z≤n) (suc c))
  where open Tools (zero VRel,_===_)
cycAt≈su {suc zero}    (suc c) = sym (su-ε (s≤s (s≤s z≤n)) (suc c))
  where open Tools (₁₊ zero VRel,_===_)
cycAt≈su {suc (suc n)} (suc c) =
  trans (cong refl (lemma-cong↑ (cycAt c) (shiftUp c) (cycAt≈su c))) (su-↑ c)
  where open Tools ((₂₊ n) VRel,_===_)

placeAt≈ : ∀ c (u : Circuit n) → (₁₊ n) ⊢ placeAt c u ≈ shiftDown c • u ↑ • shiftUp c
placeAt≈ {n} c u = cong (cycAt⁻¹≈sd c) (cong refl (cycAt≈su c))
  where open Tools ((₁₊ n) VRel,_===_)
