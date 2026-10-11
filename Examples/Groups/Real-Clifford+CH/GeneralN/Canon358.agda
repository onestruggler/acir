------------------------------------------------------------------------
-- Presentations of groups
--
-- Two crossed rotations satisfy the braid relation (Clément, Lemma D.15,
-- Equation (358))
--
-- At width 5 + k, with a = ΛXZ (4 + k) the rotation on wire 0 and
-- b = Ex • ΛZX (4 + k) • Ex the rotation on wire 1, each controlled by
-- the other's target and by the wires 2 …:
--
--   a • b • a ≈ b • a • b      (`eq358`)
--
-- No commutation of the letters of a and b reaches this (a right-angled
-- Coxeter group on them leaves the braid word reduced).  The paper's
-- idea is that a conjugation only sees the block of the conjugator where
-- all its controls are black.  So merge each rotation over every
-- colouring of the wires 2 … (`merge₂`, (354) on the top wire as in
-- RotMerge, the wires 0 1 kept black).  This gives e and e′, rotations
-- on two wires, with e • e′ • e ≈ CZ • Ex, decided on two wires.  Every
-- colouring but the black one is separated from a and b by a white wire
-- (RotAnywhere), so e = D_a • a and e′ = D_b • b with D_a, D_b passing
-- a and b (the D-trick, MergeGen.pass-last′).  Then e e′ e = D • (a b a)
-- with D = D_a D_b D_a, and CZ • Ex conjugates b to a, since
-- CZ • ZX • CZ ≈ XZ ((357)).  So D (a b a) b ≈ a D (a b a) ≈ D a (a b a),
-- and cancelling D and then a gives the braid.  Checked numerically
-- first (scratchpad r358, r5x/r24route.py).  The argument is
-- Canon358Gen's, at any width; this module supplies its merge and
-- (357) from five wires on.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.Canon358
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ) renaming (zero to 0F ; suc to sF)
open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; s≤s ; z≤n)
open import Data.Nat.Properties using (≤-refl ; ≤-trans ; n≤1+n)
open import Data.Product using (Σ ; _,_)
open import Data.Vec using ([] ; _∷_ ; _∷ʳ_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
import Examples.Groups.Real-Clifford+CH.SemanticSteps as SS
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj ; CZ² ; Ex²)
open import Examples.Groups.Real-Clifford+CH.TopWeakening using (top)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (allBits ; insertℕ ; lookupℕ)
open import Examples.Groups.Real-Clifford+CH.Encoding using (∏)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (net)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (shiftDown ; shiftUp)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires
  using (negsB ; negs² ; sdS ; net-sdS ; revS-sdS ; net-suS ; sd-target)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (placeAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceCalc using (placeAt-cong)
open import Examples.Groups.Real-Clifford+CH.GeneralN.TwoWire using (placeAt-top)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (low-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃ using (Completes)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CanonN complete₂ complete₃ using (canonN)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon ; pl)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Colours complete₂ complete₃ using (conj-swap)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (place)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX353 complete₂ complete₃ using (allT ; ∏-conj ; ∏-cong)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotAnywhere complete₂ complete₃ using (rot-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotMerge complete₂ complete₃ using (F)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX356 complete₂ complete₃ using (top⁺ ; eq357)
open import Examples.Groups.Real-Clifford+CH.GeneralN.MergeGen using (pairing ; pair-merge ; placeAt-∏ ; pass-last′)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Base358 using (e-ebe ; e-zxxz ; e-xzzx)
import Examples.Groups.Real-Clifford+CH.GeneralN.Canon358Gen as Canon358Gen

private
  ins-top : ∀ {j} (c : Bits j) b → insertℕ j b c ≡ c ∷ʳ b
  ins-top []      b = Eq.refl
  ins-top (x ∷ c) b = Eq.cong (x ∷_) (ins-top c b)

  top-F : ∀ β j → top (F β 1 ↓ᵏ j) ≡ F β 1 ↓ᵏ suc j
  top-F true  j = Eq.refl
  top-F false j = Eq.refl

------------------------------------------------------------------------
-- A rotation over every colouring of the wires 2 …, wires 0 1 black

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  merge₂ : ∀ β j → j ≤ ₃₊ k →
           (₂₊ j) ⊢ ∏ (allBits j) (λ c → negsB (true ∷ true ∷ c) • F β (suc j) • negsB (true ∷ true ∷ c))
                    ≈ F β 1 ↓ᵏ j
  merge₂ true  zero    _ = trans right-unit (trans left-unit right-unit)
    where open Tools (2 VRel,_===_)
  merge₂ false zero    _ = trans right-unit (trans left-unit right-unit)
    where open Tools (2 VRel,_===_)
  merge₂ β     (suc j) b = begin
    ∏ (allBits (suc j)) G
      ≈⟨ pairing j G ⟩
    ∏ (allBits j) (λ c → G (c ∷ʳ false) • G (c ∷ʳ true))
      ≈⟨ ∏-cong (allBits j) pair ⟩
    ∏ (allBits j) (λ c → placeAt (₂₊ j) (h c))
      ≈⟨ sym (placeAt-∏ (₂₊ j) (allBits j) h) ⟩
    placeAt (₂₊ j) (∏ (allBits j) h)
      ≈⟨ placeAt-cong (₂₊ j) (merge₂ β j (≤-trans (n≤1+n j) b)) ⟩
    placeAt (₂₊ j) (F β 1 ↓ᵏ j)
      ≈⟨ placeAt-top (F β 1 ↓ᵏ j) ⟩
    top (F β 1 ↓ᵏ j)
      ≈⟨ ≡→≈ (top-F β j) ⟩
    F β 1 ↓ᵏ suc j ∎
    where
    open Tools ((₃₊ j) VRel,_===_)
    G : Bits (suc j) → Circuit (₃₊ j)
    G c = negsB (true ∷ true ∷ c) • F β (₂₊ j) • negsB (true ∷ true ∷ c)
    h : Bits j → Circuit (₂₊ j)
    h c = negsB (true ∷ true ∷ c) • F β (suc j) • negsB (true ∷ true ∷ c)
    ≡→≈ : ∀ {x y : Circuit (₃₊ j)} → x ≡ y → x ≈ y
    ≡→≈ Eq.refl = refl
    pair : ∀ c → G (c ∷ʳ false) • G (c ∷ʳ true) ≈ placeAt (₂₊ j) (h c)
    pair c = trans (≡→≈ (Eq.cong₂ (λ x y → (negsB (true ∷ true ∷ x) • F β (₂₊ j) • negsB (true ∷ true ∷ x)) •
                                          (negsB (true ∷ true ∷ y) • F β (₂₊ j) • negsB (true ∷ true ∷ y)))
                                 (Eq.sym (ins-top c false)) (Eq.sym (ins-top c true))))
                   (pair-merge (F β (₂₊ j)) (F β (suc j)) (₂₊ j) ≤-refl (true ∷ true ∷ c)
                               (top⁺ k below β (suc j) (s≤s b)))

------------------------------------------------------------------------
-- (358): Canon358Gen's argument at width 5 + k

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    completes : Completes (₁₊ k)
    completes j≤ = below (s≤s (s≤s (s≤s (s≤s j≤))))

  eq358 : (₁₊ (₄₊ k)) ⊢ ΛXZ (₄₊ k) • (Ex ↓ • ΛZX (₄₊ k) • Ex ↓) • ΛXZ (₄₊ k)
                      ≈ (Ex ↓ • ΛZX (₄₊ k) • Ex ↓) • ΛXZ (₄₊ k) • (Ex ↓ • ΛZX (₄₊ k) • Ex ↓)
  eq358 = Canon358Gen.eq358 (canonN k completes) complete₂ (rot-comm k below)
                            (λ β → merge₂ k below β (₃₊ k) ≤-refl) (eq357 k below)
