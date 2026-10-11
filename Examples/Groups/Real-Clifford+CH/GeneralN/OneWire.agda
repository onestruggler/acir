------------------------------------------------------------------------
-- Presentations of groups
--
-- A one-wire circuit on a wire given by its number
--
-- `on1 g i` is the one-wire circuit g on wire i, in the style of
-- MultiControlled's Xat.  Everything PlaceCalc and NetWires say of X
-- holds of it: it passes every circuit one wire up (`on1-↑`), a swap
-- carries it one wire up (`on1-swap`, from the swap rules for H and Z),
-- it passes the swaps it does not touch (`on1-swap-lo`, `on1-swap-hi`),
-- under placeAt it stays below the idle wire and moves up from it
-- (`placeAt-on1-lo`, `placeAt-on1-hi`), and conjugated by a network it
-- is on the wire the network brings to its wire (`on1-net`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.OneWire where

open import Data.Fin using (Fin ; toℕ) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Nat using (ℕ ; zero ; suc ; _<_ ; _≤_ ; s≤s ; z≤n)
open import Data.Nat.Properties using (m<1+n⇒m<n∨m≡n ; ≤-refl ; ≤-trans ; n≤1+n)
open import Data.Sum using (inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj ; Ex² ; ax)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (φ ; net ; perm)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (swapAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (low-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (placeAt ; placeAt-step)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SwapCalc using (swapAt²)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (revS)

private
  variable
    n : ℕ

-- The one-wire circuit g on wire i (ε when there is no such wire).
on1 : Circuit 1 → ℕ → Circuit n
on1 {zero}  g i       = ε
on1 {suc n} g zero    = g ↓ᵏ n
on1 {suc n} g (suc i) = on1 g i ↑

------------------------------------------------------------------------
-- On wire 0

-- It passes everything one wire up.
on1-↑ : ∀ (g : Circuit 1) (u : Circuit n) → (₁₊ n) ⊢ (g ↓ᵏ n) • u ↑ ≈ u ↑ • (g ↓ᵏ n)
on1-↑ [ gate₀ () ]ʷ     u
on1-↑ [ gate₀ () ↥ ]ʷ   u
on1-↑ {n} [ gate₁ h ]ʷ u = sym (comm-gate₁-w↑ h u)
  where open Tools ((₁₊ n) VRel,_===_)
on1-↑ {n} ε u = trans left-unit (sym right-unit)
  where open Tools ((₁₊ n) VRel,_===_)
on1-↑ {n} (a • b) u = begin
  ((a ↓ᵏ n) • (b ↓ᵏ n)) • u ↑   ≈⟨ assoc ⟩
  (a ↓ᵏ n) • ((b ↓ᵏ n) • u ↑)   ≈⟨ back _ (on1-↑ b u) ⟩
  (a ↓ᵏ n) • (u ↑ • (b ↓ᵏ n))   ≈⟨ sym assoc ⟩
  ((a ↓ᵏ n) • u ↑) • (b ↓ᵏ n)   ≈⟨ front _ (on1-↑ a u) ⟩
  (u ↑ • (a ↓ᵏ n)) • (b ↓ᵏ n)   ≈⟨ assoc ⟩
  u ↑ • (a ↓ᵏ n) • (b ↓ᵏ n) ∎
  where open Tools ((₁₊ n) VRel,_===_)

private
  module SW {n : ℕ} = Conj {₂₊ n} Ex Ex²

-- The swap carries it from wire 0 to wire 1.
on1-swap : ∀ (g : Circuit 1) → (₂₊ n) ⊢ Ex • (g ↓ᵏ (₁₊ n)) • Ex ≈ (g ↓ᵏ n) ↑
on1-swap [ gate₀ () ]ʷ
on1-swap [ gate₀ () ↥ ]ʷ
on1-swap {n} [ gate₁ H-gate ]ʷ = begin
  Ex • H • Ex          ≈⟨ sym assoc ⟩
  (Ex • H) • Ex        ≈⟨ front _ (sym (ax swap-H)) ⟩
  (H ↑ • Ex) • Ex      ≈⟨ trans assoc (trans (back _ Ex²) right-unit) ⟩
  H ↑ ∎
  where open Tools ((₂₊ n) VRel,_===_)
on1-swap {n} [ gate₁ Z-gate ]ʷ = begin
  Ex • Z • Ex          ≈⟨ sym assoc ⟩
  (Ex • Z) • Ex        ≈⟨ front _ (sym (ax swap-Z)) ⟩
  (Z ↑ • Ex) • Ex      ≈⟨ trans assoc (trans (back _ Ex²) right-unit) ⟩
  Z ↑ ∎
  where open Tools ((₂₊ n) VRel,_===_)
on1-swap {n} ε = trans (back _ left-unit) Ex²
  where open Tools ((₂₊ n) VRel,_===_)
on1-swap {n} (a • b) = trans (SW.⟪⟫-• (a ↓ᵏ (₁₊ n)) (b ↓ᵏ (₁₊ n))) (cong (on1-swap a) (on1-swap b))
  where open Tools ((₂₊ n) VRel,_===_)

------------------------------------------------------------------------
-- Swaps

on1-swap-lo : ∀ (g : Circuit 1) i c → i < c → n ⊢ on1 g i • swapAt c ≈ swapAt c • on1 g i
on1-swap-lo {zero}        g i       c       _ = refl
  where open Tools (zero VRel,_===_)
on1-swap-lo {suc n}       g i       zero    ()
on1-swap-lo {suc zero}    g zero    (suc c) _ = trans right-unit (sym left-unit)
  where open Tools ((₁₊ zero) VRel,_===_)
on1-swap-lo {suc (suc n)} g zero    (suc c) _ = on1-↑ g (swapAt c)
on1-swap-lo {suc zero}    g (suc i) (suc c) _ = refl
  where open Tools ((₁₊ zero) VRel,_===_)
on1-swap-lo {suc (suc n)} g (suc i) (suc c) (s≤s p) =
  lemma-cong↑ (on1 g i • swapAt c) (swapAt c • on1 g i) (on1-swap-lo {suc n} g i c p)

on1-swap-hi : ∀ (g : Circuit 1) i c → ₂₊ c ≤ i → n ⊢ on1 g i • swapAt c ≈ swapAt c • on1 g i
on1-swap-hi {zero}        g i             c       _ = refl
  where open Tools (zero VRel,_===_)
on1-swap-hi {suc n}       g zero          c       ()
on1-swap-hi {suc n}       g (suc zero)    zero    (s≤s ())
on1-swap-hi {suc zero}    g (suc (suc i)) zero    _ = refl
  where open Tools ((₁₊ zero) VRel,_===_)
on1-swap-hi {suc (suc n)} g (suc (suc i)) zero    _ = sym (low-comm Ex (on1 g i))
  where open Tools ((₂₊ n) VRel,_===_)
on1-swap-hi {suc zero}    g (suc i)       (suc c) _ = refl
  where open Tools ((₁₊ zero) VRel,_===_)
on1-swap-hi {suc (suc n)} g (suc i)       (suc c) (s≤s p) =
  lemma-cong↑ (on1 g i • swapAt c) (swapAt c • on1 g i) (on1-swap-hi {suc n} g i c p)

-- A swap carries the gate one wire up.
on1-step : ∀ (g : Circuit 1) c → c < n → (₁₊ n) ⊢ swapAt c • on1 g c • swapAt c ≈ on1 g (suc c)
on1-step {zero}  g c ()
on1-step {suc n} g zero    _       = on1-swap g
on1-step {suc n} g (suc c) (s≤s p) =
  lemma-cong↑ (swapAt c • on1 g c • swapAt c) (on1 g (suc c)) (on1-step g c p)

------------------------------------------------------------------------
-- Under placeAt

private
  unconj-swap : ∀ c {a} → (₁₊ n) ⊢ a • swapAt c ≈ swapAt c • a → (₁₊ n) ⊢ swapAt c • a • swapAt c ≈ a
  unconj-swap {n} c {a} e = begin
    swapAt c • a • swapAt c     ≈⟨ back _ e ⟩
    swapAt c • swapAt c • a     ≈⟨ trans (sym assoc) (trans (front _ (swapAt² c)) left-unit) ⟩
    a ∎
    where open Tools ((₁₊ n) VRel,_===_)

  on1-step′ : ∀ (g : Circuit 1) c → c < n → (₁₊ n) ⊢ swapAt c • on1 g (suc c) • swapAt c ≈ on1 g c
  on1-step′ {n} g c c<n = begin
    swapAt c • on1 g (suc c) • swapAt c                       ≈⟨ back _ (front _ (sym (on1-step g c c<n))) ⟩
    swapAt c • (swapAt c • on1 g c • swapAt c) • swapAt c     ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
    (swapAt c • swapAt c) • on1 g c • (swapAt c • swapAt c)   ≈⟨ cong (swapAt² c) (back _ (swapAt² c)) ⟩
    ε • on1 g c • ε                                           ≈⟨ trans left-unit right-unit ⟩
    on1 g c ∎
    where open Tools ((₁₊ n) VRel,_===_)

placeAt-on1-lo : ∀ (g : Circuit 1) c i → i < c → c ≤ n → (₁₊ n) ⊢ placeAt {n} c (on1 g i) ≈ on1 g i
placeAt-on1-hi : ∀ (g : Circuit 1) c i → c ≤ i → c ≤ n → (₁₊ n) ⊢ placeAt {n} c (on1 g i) ≈ on1 g (suc i)

placeAt-on1-lo g zero    i () _
placeAt-on1-lo {n} g (suc c) i i<c c<n with m<1+n⇒m<n∨m≡n i<c
... | inj₁ i<c′ = begin
  placeAt (suc c) (on1 g i)                   ≈⟨ placeAt-step c (on1 g i) c<n ⟩
  swapAt c • placeAt c (on1 g i) • swapAt c   ≈⟨ back _ (front _ (placeAt-on1-lo g c i i<c′ (≤-trans (n≤1+n c) c<n))) ⟩
  swapAt c • on1 g i • swapAt c               ≈⟨ unconj-swap c (on1-swap-lo g i c i<c′) ⟩
  on1 g i ∎
  where open Tools ((₁₊ n) VRel,_===_)
... | inj₂ Eq.refl = begin
  placeAt (suc c) (on1 g c)                   ≈⟨ placeAt-step c (on1 g c) c<n ⟩
  swapAt c • placeAt c (on1 g c) • swapAt c   ≈⟨ back _ (front _ (placeAt-on1-hi g c c ≤-refl (≤-trans (n≤1+n c) c<n))) ⟩
  swapAt c • on1 g (suc c) • swapAt c         ≈⟨ on1-step′ g c c<n ⟩
  on1 g c ∎
  where open Tools ((₁₊ n) VRel,_===_)

placeAt-on1-hi {n} g zero    i _ _ = trans left-unit right-unit
  where open Tools ((₁₊ n) VRel,_===_)
placeAt-on1-hi {n} g (suc c) i c<i c<n = begin
  placeAt (suc c) (on1 g i)                   ≈⟨ placeAt-step c (on1 g i) c<n ⟩
  swapAt c • placeAt c (on1 g i) • swapAt c   ≈⟨ back _ (front _ (placeAt-on1-hi g c i (≤-trans (n≤1+n c) c<i) (≤-trans (n≤1+n c) c<n))) ⟩
  swapAt c • on1 g (suc i) • swapAt c         ≈⟨ unconj-swap c (on1-swap-hi g (suc i) c (s≤s c<i)) ⟩
  on1 g (suc i) ∎
  where open Tools ((₁₊ n) VRel,_===_)

------------------------------------------------------------------------
-- Across a network

private
  gen² : (h : S.Gen n) → n ⊢ φ h • φ h ≈ ε
  gen² (S.gate₀ ())
  gen² (S.gate₁ ())
  gen² (S.gate₂ S.σ-gate) = Ex²
  gen² (h S.↥)            = lemma-cong↑ (φ h • φ h) ε (gen² h)

  gen-on1 : ∀ (g : Circuit 1) (h : S.Gen n) (j : Fin n) →
            n ⊢ φ h • on1 g (toℕ (perm [ h ]ʷ ⟨$⟩ʳ j)) • φ h ≈ on1 g (toℕ j)
  gen-on1 g (S.gate₀ ())
  gen-on1 g (S.gate₁ ())
  gen-on1 {₂₊ n} g (S.gate₂ S.σ-gate) 0F = begin
    Ex • (g ↓ᵏ n) ↑ • Ex                             ≈⟨ back _ (front _ (sym (on1-swap g))) ⟩
    Ex • (Ex • (g ↓ᵏ (₁₊ n)) • Ex) • Ex              ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
    (Ex • Ex) • (g ↓ᵏ (₁₊ n)) • (Ex • Ex)            ≈⟨ cong Ex² (back _ Ex²) ⟩
    ε • (g ↓ᵏ (₁₊ n)) • ε                            ≈⟨ trans left-unit right-unit ⟩
    g ↓ᵏ (₁₊ n) ∎
    where open Tools ((₂₊ n) VRel,_===_)
  gen-on1 {₂₊ n} g (S.gate₂ S.σ-gate) (sF 0F) = on1-swap g
  gen-on1 {₂₊ n} g (S.gate₂ S.σ-gate) (sF (sF k)) = begin
    Ex • on1 g (toℕ k) ↑ ↑ • Ex     ≈⟨ sym assoc ⟩
    (Ex • on1 g (toℕ k) ↑ ↑) • Ex   ≈⟨ front _ (low-comm Ex (on1 g (toℕ k))) ⟩
    (on1 g (toℕ k) ↑ ↑ • Ex) • Ex   ≈⟨ trans assoc (trans (back _ Ex²) right-unit) ⟩
    on1 g (toℕ k) ↑ ↑ ∎
    where open Tools ((₂₊ n) VRel,_===_)
  gen-on1 {₁₊ n} g (h S.↥) 0F = begin
    φ h ↑ • (g ↓ᵏ n) • φ h ↑       ≈⟨ back _ (on1-↑ g (φ h)) ⟩
    φ h ↑ • φ h ↑ • (g ↓ᵏ n)       ≈⟨ trans (sym assoc) (trans (front _ (lemma-cong↑ (φ h • φ h) ε (gen² h))) left-unit) ⟩
    g ↓ᵏ n ∎
    where open Tools ((₁₊ n) VRel,_===_)
  gen-on1 {₁₊ n} g (h S.↥) (sF j) =
    lemma-cong↑ (φ h • on1 g (toℕ (perm [ h ]ʷ ⟨$⟩ʳ j)) • φ h) (on1 g (toℕ j)) (gen-on1 g h j)

on1-net : ∀ (g : Circuit 1) (u : Word (S.Gen n)) (j : Fin n) →
          n ⊢ net u • on1 g (toℕ (perm u ⟨$⟩ʳ j)) • net (revS u) ≈ on1 g (toℕ j)
on1-net g [ h ]ʷ j = gen-on1 g h j
on1-net {n} g ε j = trans left-unit right-unit
  where open Tools (n VRel,_===_)
on1-net {n} g (u • v) j = begin
  (net u • net v) • on1 g (toℕ (perm v ⟨$⟩ʳ (perm u ⟨$⟩ʳ j))) • (net (revS v) • net (revS u))
    ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
  net u • (net v • on1 g (toℕ (perm v ⟨$⟩ʳ (perm u ⟨$⟩ʳ j))) • net (revS v)) • net (revS u)
    ≈⟨ back _ (front _ (on1-net g v (perm u ⟨$⟩ʳ j))) ⟩
  net u • on1 g (toℕ (perm u ⟨$⟩ʳ j)) • net (revS u)
    ≈⟨ on1-net g u j ⟩
  on1 g (toℕ j) ∎
  where open Tools (n VRel,_===_)
