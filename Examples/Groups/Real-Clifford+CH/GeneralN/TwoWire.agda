------------------------------------------------------------------------
-- Presentations of groups
--
-- A two-wire circuit on the wires i and i + 1
--
-- `on2 g i` is the two-wire circuit g on the wires i and i + 1, as
-- OneWire's `on1` is a one-wire one.  What Lemma 8.7 needs of it: it
-- passes the swaps below it (`on2-swap-hi`) and so the network that
-- brings a lower wire to 0 (`pl-sd-on2`); placeAt below it carries it
-- one wire up (`placeAt-on2-hi`); and placeAt at the top leaves it where
-- it is (`placeAt-top`: placeAt at the top is TopWeakening's `top`, the
-- gate under one more idle wire, by the naturality of the cycle `σ`).
-- Placing in between would separate its two wires, and is not needed.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.TwoWire where

open import Data.Nat using (ℕ ; zero ; suc ; _<_ ; _≤_ ; s≤s ; z≤n)
open import Data.Nat.Properties using (≤-refl ; ≤-trans ; n≤1+n)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

import Presentation.Base as PB
import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; Ex²)
open import Examples.Groups.Real-Clifford+CH.TopWeakening using (_↧ ; top ; σ ; σ⁻¹ ; σσ⁻¹ ; σ⁻¹σ ; nat)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (net)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (swapAt ; shiftDown ; shiftUp)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (low-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (placeAt ; placeAt-step ; cycAt ; cycAt⁻¹)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SwapCalc using (swapAt² ; placeAt≈ ; sd-above ; su-above)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (sdS ; revS ; net-sdS ; net-suS ; revS-sdS ; net-inv)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (pl)

private
  variable
    n : ℕ

-- The two-wire circuit g on the wires i and i + 1 (ε when there are no
-- such wires).  The clause on `suc i` comes first, so that it reduces at
-- a symbolic width.
on2 : Circuit 2 → ℕ → Circuit n
on2 {zero}        g i       = ε
on2 {suc n}       g (suc i) = on2 g i ↑
on2 {suc zero}    g zero    = ε
on2 {suc (suc n)} g zero    = g ↓ᵏ n

------------------------------------------------------------------------
-- The swaps below it

on2-swap-hi : ∀ (g : Circuit 2) i c → ₂₊ c ≤ i → n ⊢ on2 g i • swapAt c ≈ swapAt c • on2 g i
on2-swap-hi {zero}        g i             c       _ = refl
  where open Tools (zero VRel,_===_)
on2-swap-hi {suc n}       g zero          c       ()
on2-swap-hi {suc n}       g (suc zero)    c       (s≤s ())
on2-swap-hi {suc zero}    g (suc (suc i)) zero    _ = refl
  where open Tools ((₁₊ zero) VRel,_===_)
on2-swap-hi {suc (suc n)} g (suc (suc i)) zero    _ = sym (low-comm Ex (on2 g i))
  where open Tools ((₂₊ n) VRel,_===_)
on2-swap-hi {suc zero}    g (suc i)       (suc c) _ = refl
  where open Tools ((₁₊ zero) VRel,_===_)
on2-swap-hi {suc (suc n)} g (suc i)       (suc c) (s≤s p) =
  lemma-cong↑ (on2 g i • swapAt c) (swapAt c • on2 g i) (on2-swap-hi {suc n} g i c p)

-- The shift that brings a wire below it to 0.
sd-on2 : ∀ (g : Circuit 2) j i → j < i → n ⊢ shiftDown j • on2 g i ≈ on2 g i • shiftDown j
sd-on2 {n} g zero    i _   = trans left-unit (sym right-unit)
  where open Tools (n VRel,_===_)
sd-on2 {n} g (suc j) i j<i = begin
  (swapAt j • shiftDown j) • on2 g i    ≈⟨ trans assoc (back _ (sd-on2 g j i (≤-trans (n≤1+n _) j<i))) ⟩
  swapAt j • (on2 g i • shiftDown j)    ≈⟨ trans (sym assoc) (front _ (sym (on2-swap-hi g i j j<i))) ⟩
  (on2 g i • swapAt j) • shiftDown j    ≈⟨ assoc ⟩
  on2 g i • swapAt j • shiftDown j ∎
  where open Tools (n VRel,_===_)

pl-sd-on2 : ∀ (g : Circuit 2) j i → j < i → n ⊢ pl (sdS j) (on2 g i) ≈ on2 g i
pl-sd-on2 {n} g j i j<i = begin
  net (sdS j) • on2 g i • net (revS (sdS j))     ≈⟨ sym assoc ⟩
  (net (sdS j) • on2 g i) • net (revS (sdS j))   ≈⟨ front _ (Eq.subst (λ w → w • on2 g i ≈ on2 g i • w) (Eq.sym (net-sdS j))
                                                                       (sd-on2 g j i j<i)) ⟩
  (on2 g i • net (sdS j)) • net (revS (sdS j))   ≈⟨ trans assoc (trans (back _ (net-inv (sdS j))) right-unit) ⟩
  on2 g i ∎
  where open Tools (n VRel,_===_)

------------------------------------------------------------------------
-- Under placeAt

private
  unconj-swap : ∀ c {a} → (₁₊ n) ⊢ a • swapAt c ≈ swapAt c • a → (₁₊ n) ⊢ swapAt c • a • swapAt c ≈ a
  unconj-swap {n} c {a} e = begin
    swapAt c • a • swapAt c     ≈⟨ back _ e ⟩
    swapAt c • swapAt c • a     ≈⟨ trans (sym assoc) (trans (front _ (swapAt² c)) left-unit) ⟩
    a ∎
    where open Tools ((₁₊ n) VRel,_===_)

-- An idle wire below it carries it one wire up.
placeAt-on2-hi : ∀ (g : Circuit 2) c i → c ≤ i → c ≤ n → (₁₊ n) ⊢ placeAt {n} c (on2 g i) ≈ on2 g (suc i)
placeAt-on2-hi {n} g zero    i _ _ = trans left-unit right-unit
  where open Tools ((₁₊ n) VRel,_===_)
placeAt-on2-hi {n} g (suc c) i c<i c<n = begin
  placeAt (suc c) (on2 g i)                   ≈⟨ placeAt-step c (on2 g i) c<n ⟩
  swapAt c • placeAt c (on2 g i) • swapAt c   ≈⟨ back _ (front _ (placeAt-on2-hi g c i (≤-trans (n≤1+n c) c<i) (≤-trans (n≤1+n c) c<n))) ⟩
  swapAt c • on2 g (suc i) • swapAt c         ≈⟨ unconj-swap c (on2-swap-hi g (suc i) c (s≤s c<i)) ⟩
  on2 g (suc i) ∎
  where open Tools ((₁₊ n) VRel,_===_)

-- placeAt at the top is `top`.
private
  cyc≡σ : ∀ n → cycAt {₁₊ n} n ≡ σ n
  cyc≡σ zero    = Eq.refl
  cyc≡σ (suc n) = Eq.cong (λ w → Ex ↓ • w ↑) (cyc≡σ n)

  cyc⁻¹≡σ⁻¹ : ∀ n → cycAt⁻¹ {₁₊ n} n ≡ σ⁻¹ n
  cyc⁻¹≡σ⁻¹ zero    = Eq.refl
  cyc⁻¹≡σ⁻¹ (suc n) = Eq.cong (λ w → w ↑ • Ex ↓) (cyc⁻¹≡σ⁻¹ n)

placeAt-top : ∀ (w : Circuit n) → (₁₊ n) ⊢ placeAt n w ≈ top w
placeAt-top {n} w = begin
  cycAt⁻¹ n • w ↑ • cycAt n     ≈⟨ ≡→≈ (Eq.cong₂ (λ a b → a • w ↑ • b) (cyc⁻¹≡σ⁻¹ n) (cyc≡σ n)) ⟩
  σ⁻¹ n • w ↑ • σ n             ≈⟨ back _ (nat w) ⟩
  σ⁻¹ n • σ n • top w           ≈⟨ trans (sym assoc) (trans (front _ (σ⁻¹σ n)) left-unit) ⟩
  top w ∎
  where
  open Tools ((₁₊ n) VRel,_===_)
  ≡→≈ : ∀ {a b : Circuit (₁₊ n)} → a ≡ b → a ≈ b
  ≡→≈ Eq.refl = refl

-- `top` leaves it where it is.
top-↑ : ∀ (w : Circuit n) → top (w ↑) ≡ top w ↑
top-↑ [ g ]ʷ  = Eq.refl
top-↑ ε       = Eq.refl
top-↑ (u • v) = Eq.cong₂ _•_ (top-↑ u) (top-↑ v)

top-↓ : ∀ (g : Circuit 2) → top (g ↓ᵏ n) ≡ g ↓ᵏ (suc n)
top-↓ [ gate₀ () ]ʷ
top-↓ [ gate₀ () ↥ ]ʷ
top-↓ [ gate₀ () ↥ ↥ ]ʷ
top-↓ [ gate₁ h ]ʷ    = Eq.refl
top-↓ [ gate₂ h ]ʷ    = Eq.refl
top-↓ [ gate₁ h ↥ ]ʷ  = Eq.refl
top-↓ ε               = Eq.refl
top-↓ (u • v)         = Eq.cong₂ _•_ (top-↓ u) (top-↓ v)

top-on2 : ∀ (g : Circuit 2) i → ₂₊ i ≤ n → top (on2 {n} g i) ≡ on2 {₁₊ n} g i
top-on2 {zero}        g i       ()
top-on2 {suc zero}    g i       (s≤s ())
top-on2 {suc (suc n)} g zero    _       = top-↓ g
top-on2 {suc (suc n)} g (suc i) (s≤s p) = Eq.trans (top-↑ (on2 g i)) (Eq.cong _↑ (top-on2 g i p))

-- With an idle wire on top.
placeAt-on2-top : ∀ (g : Circuit 2) i → ₂₊ i ≤ n → (₁₊ n) ⊢ placeAt n (on2 g i) ≈ on2 g i
placeAt-on2-top {n} g i p = Eq.subst (λ w → (₁₊ n) ⊢ placeAt n (on2 g i) ≈ w) (top-on2 g i p) (placeAt-top (on2 g i))

------------------------------------------------------------------------
-- The network sdS c on a circuit one wire up is placeAt c

pl-sd-↑ : ∀ c (w : Circuit n) → (₁₊ n) ⊢ pl (sdS c) (w ↑) ≈ placeAt c w
pl-sd-↑ {n} c w = Eq.subst₂ (λ a b → a • w ↑ • b ≈ placeAt c w) (Eq.sym (net-sdS c))
                            (Eq.sym (Eq.trans (Eq.cong net (revS-sdS c)) (net-suS c)))
                            (sym (placeAt≈ c w))
  where open Tools ((₁₊ n) VRel,_===_)

------------------------------------------------------------------------
-- The pair of swaps above it carries it one wire up

private
  step₀ : ∀ (g : Circuit 2) → (₃₊ n) ⊢ Ex • Ex ↑ • (g ↓ᵏ (suc n)) • Ex ↑ • Ex ≈ (g ↓ᵏ n) ↑
  step₀ {n} g = begin
    Ex • Ex ↑ • B • Ex ↑ • Ex
      ≈⟨ by-passoc (□ • □ • □ • □ • □) ((□ • □ • □) • □ • □) Eq.refl ⟩
    (Ex • Ex ↑ • B) • Ex ↑ • Ex
      ≈⟨ front _ (sym key) ⟩
    (A ↑ • Ex • Ex ↑) • Ex ↑ • Ex
      ≈⟨ by-passoc ((□ • □ • □) • □ • □) (□ • □ • (□ • □) • □) Eq.refl ⟩
    A ↑ • Ex • (Ex ↑ • Ex ↑) • Ex
      ≈⟨ back _ (back _ (trans (front _ (lemma-cong↑ (Ex • Ex) ε Ex²)) left-unit)) ⟩
    A ↑ • Ex • Ex
      ≈⟨ trans (back _ Ex²) right-unit ⟩
    A ↑ ∎
    where
    open Tools ((₃₊ n) VRel,_===_)
    A : Circuit (₂₊ n)
    A = g ↓ᵏ n
    B S S⁻ : Circuit (₃₊ n)
    B  = g ↓ᵏ (suc n)
    S  = σ n ↑ ↑
    S⁻ = σ⁻¹ n ↑ ↑
    nat′ : A ↑ • (Ex • (Ex ↑ • S)) ≈ (Ex • (Ex ↑ • S)) • B
    nat′ = Eq.subst (λ w → A ↑ • (Ex • (Ex ↑ • S)) ≈ (Ex • (Ex ↑ • S)) • w) (top-↓ g) (nat A)
    SS⁻ : S • S⁻ ≈ ε
    SS⁻ = lemma-cong↑ ((σ n • σ⁻¹ n) ↑) ε (lemma-cong↑ (σ n • σ⁻¹ n) ε (σσ⁻¹ n))
    key : A ↑ • Ex • Ex ↑ ≈ Ex • Ex ↑ • B
    key = begin
      A ↑ • Ex • Ex ↑
        ≈⟨ sym (trans (back _ SS⁻) right-unit) ⟩
      (A ↑ • Ex • Ex ↑) • (S • S⁻)
        ≈⟨ by-passoc ((□ • □ • □) • (□ • □)) ((□ • (□ • (□ • □))) • □) Eq.refl ⟩
      (A ↑ • (Ex • (Ex ↑ • S))) • S⁻
        ≈⟨ front _ nat′ ⟩
      ((Ex • (Ex ↑ • S)) • B) • S⁻
        ≈⟨ by-passoc (((□ • (□ • □)) • □) • □) ((□ • □ • (□ • □)) • □) Eq.refl ⟩
      (Ex • Ex ↑ • (S • B)) • S⁻
        ≈⟨ front _ (back _ (back _ (sym (low-comm g (σ n))))) ⟩
      (Ex • Ex ↑ • (B • S)) • S⁻
        ≈⟨ by-passoc ((□ • □ • (□ • □)) • □) ((□ • □ • □) • (□ • □)) Eq.refl ⟩
      (Ex • Ex ↑ • B) • (S • S⁻)
        ≈⟨ trans (back _ SS⁻) right-unit ⟩
      Ex • Ex ↑ • B ∎

on2-step : ∀ (g : Circuit 2) j → j ≤ n →
           (₃₊ n) ⊢ swapAt j • swapAt (suc j) • on2 g j • swapAt (suc j) • swapAt j ≈ on2 g (suc j)
on2-step g zero    _       = step₀ g
on2-step {suc n} g (suc j) (s≤s p) =
  lemma-cong↑ (swapAt j • swapAt (suc j) • on2 g j • swapAt (suc j) • swapAt j) (on2 g (suc j)) (on2-step g j p)

-- The network of Definition 2.4 that brings wire j to 0 and j + 1 to 1
-- carries the gate on the wires 0, 1 to the wires j, j + 1.
pair-down : ∀ (g : Circuit 2) j → j ≤ suc n →
            (₃₊ n) ⊢ (shiftDown j • shiftDown j ↑) • on2 g 0 • (shiftUp j ↑ • shiftUp j) ≈ on2 g j
pair-down {n} g zero    _ = trans (cong left-unit (trans (back _ left-unit) right-unit)) left-unit
  where open Tools ((₃₊ n) VRel,_===_)
pair-down {n} g (suc j) (s≤s p) = begin
  ((s • D) • (s′ • D ↑)) • X • ((U ↑ • s′) • (U • s))
    ≈⟨ by-passoc (((□ • □) • (□ • □)) • □ • ((□ • □) • (□ • □))) ((□ • (□ • □) • □) • □ • (□ • (□ • □) • □)) Eq.refl ⟩
  (s • (D • s′) • D ↑) • X • (U ↑ • (s′ • U) • s)
    ≈⟨ cong (back _ (front _ (sym (sd-above j (suc j) ≤-refl′))))
            (back _ (back _ (front _ (sym (su-above j (suc j) ≤-refl′))))) ⟩
  (s • (s′ • D) • D ↑) • X • (U ↑ • (U • s′) • s)
    ≈⟨ by-passoc ((□ • (□ • □) • □) • □ • (□ • (□ • □) • □)) (□ • □ • ((□ • □) • □ • (□ • □)) • □ • □) Eq.refl ⟩
  s • s′ • ((D • D ↑) • X • (U ↑ • U)) • s′ • s
    ≈⟨ back _ (back _ (front _ (pair-down g j (≤-trans (n≤1+n j) (s≤s p′))))) ⟩
  s • s′ • on2 g j • s′ • s
    ≈⟨ on2-step g j p′ ⟩
  on2 g (suc j) ∎
  where
  open Tools ((₃₊ n) VRel,_===_)
  p′ : j ≤ n
  p′ = p
  ≤-refl′ : j < suc j
  ≤-refl′ = s≤s ≤-refl
  s s′ D U X : Circuit (₃₊ n)
  s  = swapAt j
  s′ = swapAt (suc j)
  D  = shiftDown j
  U  = shiftUp j
  X  = on2 g 0
