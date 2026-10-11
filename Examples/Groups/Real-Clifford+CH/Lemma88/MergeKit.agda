------------------------------------------------------------------------
-- Presentations of groups
--
-- A rotation merged over every colouring of its controls, at any width
-- with the top merges given (Clément, Appendix E.3, the products in the
-- proof of Lemma 8.5)
--
-- Given (354) on the top wire at every width up to 3 + m (`tm`), the
-- rotation on 3 + m wires over every colouring of its controls is ZX,
-- resp. XZ, on wire 0 (`mergeN`, MergeGen.MergeTop), and over every
-- colouring of the wires 2 … with wire 1 kept a black control it is the
-- two-wire rotation (`merge₁R`).  DecX supplies `tm` from five wires on;
-- below that it comes from Lemmas D.2 and D.5.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; _<_)
open import Notations using (₂₊)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (TopMerge)

module Examples.Groups.Real-Clifford+CH.Lemma88.MergeKit
  {m : ℕ} (tm : ∀ β K → K < ₂₊ m → TopMerge β K)
  where

open import Data.Bool using (Bool ; true ; false)
open import Data.Nat using (zero ; suc ; _≤_ ; s≤s)
open import Data.Nat.Properties using (≤-refl ; ≤-trans ; n≤1+n)
open import Data.Vec using (_∷_ ; _∷ʳ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

open import Notations using (₁₊ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.TopWeakening using (top)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (allBits ; insertℕ)
open import Examples.Groups.Real-Clifford+CH.Encoding using (∏)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (placeAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceCalc using (placeAt-cong)
open import Examples.Groups.Real-Clifford+CH.GeneralN.TwoWire using (placeAt-top)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (F)
open import Examples.Groups.Real-Clifford+CH.GeneralN.MergeGen
  using (module MergeTop ; pairing ; pair-merge ; placeAt-∏ ; ∏-cong)

private
  N : ℕ
  N = ₃₊ m

------------------------------------------------------------------------
-- Wire 1 kept a black control

private
  ins-top : ∀ {j} (c : Bits j) b → insertℕ j b c ≡ c ∷ʳ b
  ins-top Data.Vec.[] b = Eq.refl
  ins-top (x ∷ c)     b = Eq.cong (x ∷_) (ins-top c b)

  top-↓ : ∀ β j → top (F β 1 ↓ᵏ j) ≡ F β 1 ↓ᵏ suc j
  top-↓ true  j = Eq.refl
  top-↓ false j = Eq.refl

  base : ∀ β → 2 ⊢ ∏ (allBits 0) (λ c → negsB (true ∷ true ∷ c) • F β 1 • negsB (true ∷ true ∷ c)) ≈ F β 1 ↓ᵏ 0
  base true  = trans right-unit (trans left-unit right-unit)
    where open Tools (2 VRel,_===_)
  base false = trans right-unit (trans left-unit right-unit)
    where open Tools (2 VRel,_===_)

-- The rotation over every colouring of the wires 2 …, wire 1 kept a
-- black control: the two-wire rotation.  merge-top₀ with two bottom
-- wires.
merge₁R : ∀ β j → j ≤ ₁₊ m →
          (₂₊ j) ⊢ ∏ (allBits j) (λ c → negsB (true ∷ true ∷ c) • F β (₁₊ j) • negsB (true ∷ true ∷ c))
                   ≈ F β 1 ↓ᵏ j
merge₁R β zero    _ = base β
merge₁R β (suc j) b = begin
  ∏ (allBits (suc j)) G
    ≈⟨ pairing j G ⟩
  ∏ (allBits j) (λ c → G (c ∷ʳ false) • G (c ∷ʳ true))
    ≈⟨ ∏-cong (allBits j) pair ⟩
  ∏ (allBits j) (λ c → placeAt (₂₊ j) (h c))
    ≈⟨ sym (placeAt-∏ (₂₊ j) (allBits j) h) ⟩
  placeAt (₂₊ j) (∏ (allBits j) h)
    ≈⟨ placeAt-cong (₂₊ j) (merge₁R β j (≤-trans (n≤1+n j) b)) ⟩
  placeAt (₂₊ j) (F β 1 ↓ᵏ j)
    ≈⟨ trans (placeAt-top (F β 1 ↓ᵏ j)) (≡→≈ (top-↓ β j)) ⟩
  F β 1 ↓ᵏ suc j ∎
  where
  open Tools ((₃₊ j) VRel,_===_)
  G : Bits (suc j) → Circuit (₃₊ j)
  G c = negsB (true ∷ true ∷ c) • F β (₂₊ j) • negsB (true ∷ true ∷ c)
  h : Bits j → Circuit (₂₊ j)
  h c = negsB (true ∷ true ∷ c) • F β (₁₊ j) • negsB (true ∷ true ∷ c)
  ≡→≈ : ∀ {x y : Circuit (₃₊ j)} → x ≡ y → x ≈ y
  ≡→≈ Eq.refl = refl
  pair : ∀ c → G (c ∷ʳ false) • G (c ∷ʳ true) ≈ placeAt (₂₊ j) (h c)
  pair c = trans (≡→≈ (Eq.cong₂ (λ x y → (negsB (true ∷ true ∷ x) • F β (₂₊ j) • negsB (true ∷ true ∷ x)) •
                                         (negsB (true ∷ true ∷ y) • F β (₂₊ j) • negsB (true ∷ true ∷ y)))
                                (Eq.sym (ins-top c false)) (Eq.sym (ins-top c true))))
                 (pair-merge (F β (₂₊ j)) (F β (₁₊ j)) (₂₊ j) ≤-refl (true ∷ true ∷ c) (tm β (₁₊ j) (s≤s b)))

------------------------------------------------------------------------
-- Every control merged

mergeN : ∀ β → N ⊢ ∏ (allBits (₂₊ m)) (λ c → negsB (true ∷ c) • F β (₂₊ m) • negsB (true ∷ c))
                 ≈ F β 0 ↓ᵏ (₂₊ m)
mergeN true  = MergeTop.merge-top₀ (F true) (₂₊ m) (tm true) Eq.refl (λ j → Eq.refl) (₂₊ m) ≤-refl
mergeN false = MergeTop.merge-top₀ (F false) (₂₊ m) (tm false) Eq.refl (λ j → Eq.refl) (₂₊ m) ≤-refl
