------------------------------------------------------------------------
-- Presentations of groups
--
-- CZ, the bilinear quadratic phase
--
-- CZ = S⁻¹ • S⁻¹ ↑ • P (Definition 16), P the gadget of S on x₀ + x₁
-- (Phase.Quad.S), is a product of commuting diagonal gates, so it
-- commutes with S and Z on both wires (CZ∥…), its iterates are those of
-- its factors (CZ^), it has order p, and SWAP fixes it (CZ-sym, the
-- paper's CZ-SWAP, from the two readings of P).  Moving past the affine
-- generators substitutes into its phase x₀ x₁:
--
--   CZ-X     X on a wire leaves Z on the other (the paper's CZ-X);
--   CZ-CX    CX⁻¹ CZ CX = S² ↑ Z ↑ CZ (the paper's CZ-CX), by
--            conjugating with M₋₁ on the control, which inverts CX
--            (rule (4)) and CZ (rule (28));
--   CZ-gad   CX⁻ᵗ S CXᵗ = S (Sᵗ²) ↑ (Zᵗ⁽ᵗ⁻¹⁾ᐟ²) ↑ CZᵗ, by induction from CZ-CX
--            (the paper's CZ-S-gadget);
--   CZ-M     a multiplier scales it (the paper's CZ-M).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Phase.Quad.CZ
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) (h : 2 ≤ lv) where

open import Data.Fin.Base using (toℕ)
open import Data.Nat.Base using (zero ; suc)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_ ; _^_)

open import Notations using (₁₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
  using (F ; F* ; p ; 0F ; 1F ; 2F ; _+_ ; _*_ ; -_ ; -1* ; binom2 ; module FR)
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Powers p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Lib p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Wires p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Affine p-2 p-prime lv using (CX-X)
open import Examples.Groups.Qupit-Phase-Affine.Phase.Quad.S p-2 p-prime lv h public

private
  variable
    n : ℕ

  h₁ : 1 ≤ lv
  h₁ = lin₂ h

-- A power of a word of order p has order p.
pow-order : ∀ {m} {w : Circuit m} → m ⊢ w ^ p ≈ ε → (i : ℕ) → m ⊢ (w ^ i) ^ p ≈ ε
pow-order {m} {w} wp i = begin
  (w ^ i) ^ p              ≈⟨ Pow.pow-pow m w i p ⟩
  w ^ (p ℕ.* i)            ≈⟨ refl' (Eq.cong (w ^_) (ℕP.*-comm p i)) ⟩
  w ^ (i ℕ.* p)            ≈⟨ Pow.pow-*d m w p i ⟩
  (w ^ p) ^ i              ≈⟨ trans (Pow.pow-cong m i wp) (Pow.pow-ε m i) ⟩
  ε                        ∎
  where open Width m

------------------------------------------------------------------------
-- The factors of CZ commute

module _ {n : ℕ} where

  open Width (₂₊ n)

  private
    Si₀ Si₁ Ci : Circuit (₂₊ n)
    Si₀ = S h ^ᶠ (- 1F)
    Si₁ = (S h ^ᶠ (- 1F)) ↑
    Ci  = CX ^ᶠ (- 1F)

    -- A lifted iterate inherits a commutation of the lifted gate.
    up-iter : (w : Circuit (₁₊ n)) {y : Circuit (₂₊ n)} (k : F) → (₂₊ n) ⊢ w ↑ ∥ y → (₂₊ n) ⊢ (w ^ᶠ k) ↑ ∥ y
    up-iter w k e = trans (front _ (refl' (↑ᶠ w k)))
                      (trans (∥-^ᶠ k e) (back _ (refl' (Eq.sym (↑ᶠ w k)))))

  Si₀∥Si₁ : (₂₊ n) ⊢ Si₀ ∥ Si₁
  Si₀∥Si₁ = Sᶠ-up (- 1F) (S h ^ᶠ (- 1F))

  Si₀∥P : (₂₊ n) ⊢ Si₀ ∥ P
  Si₀∥P = ∥-^ᶠ (- 1F) S∥P

  Si₁∥P : (₂₊ n) ⊢ Si₁ ∥ P
  Si₁∥P = up-iter (S h) (- 1F) S↑∥P

  -- So CZ commutes with S and Z on both wires.
  private
    ∥CZ : {x : Circuit (₂₊ n)} → (₂₊ n) ⊢ x ∥ Si₀ → (₂₊ n) ⊢ x ∥ Si₁ → (₂₊ n) ⊢ x ∥ P → (₂₊ n) ⊢ x ∥ CZ h
    ∥CZ a b c = ∥-• a (∥-• b c)

  S∥CZ : (₂₊ n) ⊢ S h ∥ CZ h
  S∥CZ = ∥CZ (∥-sym (∥-^ᶠ (- 1F) Width.refl)) (Sᶠ-up 1F (S h ^ᶠ (- 1F))) S∥P

  S↑∥CZ : (₂₊ n) ⊢ S h ↑ ∥ CZ h
  S↑∥CZ = ∥CZ (∥-sym Si₀∥S↑) (lift (Width.sym (∥-^ᶠ (- 1F) Width.refl))) S↑∥P
    where
    Si₀∥S↑ : (₂₊ n) ⊢ Si₀ ∥ S h ↑
    Si₀∥S↑ = Sᶠ-up (- 1F) (S h)

  Z∥CZ : (₂₊ n) ⊢ Z h₁ ∥ CZ h
  Z∥CZ = ∥CZ (∥-sym (Sᶠ∥Zᶠ (- 1F) 1F)) (Zᶠ-up 1F (S h ^ᶠ (- 1F))) Z∥P

  Z↑∥CZ : (₂₊ n) ⊢ Z h₁ ↑ ∥ CZ h
  Z↑∥CZ = ∥CZ (∥-sym (Sᶠ-up (- 1F) (Z h₁))) (lift (∥-sym (Sᶠ∥Zᶠ (- 1F) 1F))) Z↑∥P

  ----------------------------------------------------------------------
  -- Iterates and order

  CZ^ : (k : ℕ) → (₂₊ n) ⊢ CZ h ^ k ≈ Si₀ ^ k • Si₁ ^ k • P ^ k
  CZ^ k = trans (Pow.pow-• (₂₊ n) k (∥-• Si₀∥Si₁ Si₀∥P)) (back _ (Pow.pow-• (₂₊ n) k Si₁∥P))

  CZ-order : (₂₊ n) ⊢ CZ h ^ p ≈ ε
  CZ-order = begin
    CZ h ^ p                         ≈⟨ CZ^ p ⟩
    Si₀ ^ p • Si₁ ^ p • P ^ p        ≈⟨ cong (pow-order S-order (toℕ (- 1F)))
                                            (cong (trans (refl' (Eq.sym (↑-pow (S h ^ᶠ (- 1F)) p)))
                                                         (lift (pow-order S-order (toℕ (- 1F)))))
                                                  (trans (P^ p) (back _ (trans (front _ S-order) left-unit)))) ⟩
    ε • ε • Ci • CX                  ≈⟨ trans left-unit (trans left-unit (CX-invˡ 1F)) ⟩
    ε                                ∎

  ----------------------------------------------------------------------
  -- SWAP fixes CZ

  private
    sP : (₂₊ n) ⊢ SWAP • P ≈ P • SWAP
    sP = trans (slide (slideᶠ (- 1F) sCX) (slide sS sCX)) (front _ (sym P≈P′))

  CZ-sym : (₂₊ n) ⊢ SWAP • CZ h ≈ CZ h • SWAP
  CZ-sym = begin
    SWAP • Si₀ • Si₁ • P                 ≈⟨ slide (sSᶠ (- 1F)) (slide (sS↑ᶠ (- 1F)) sP) ⟩
    (Si₁ • Si₀ • P) • SWAP               ≈⟨ front _ (trans (sym assoc) (trans (front _ (sym Si₀∥Si₁)) assoc)) ⟩
    (Si₀ • Si₁ • P) • SWAP               ∎

  ----------------------------------------------------------------------
  -- CZ past X

  private
    -- Rule (21) as a conjugation.
    CZ₀-conj : (₂₊ n) ⊢ Ci • Z h₁ • CX ≈ Z h₁ • Z h₁ ↑
    CZ₀-conj = sym (trans (sym (cancel-in (CX-invˡ 1F) _)) (back _ (ax (ax21 h₁))))

    P-X : (₂₊ n) ⊢ P • X ≈ X • Z h₁ • Z h₁ ↑ • P
    P-X = begin
      (Ci • S h • CX) • X                  ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • □ • □) Eq.refl ⟩
      Ci • S h • CX • X                    ≈⟨ back _ (back _ CX-X) ⟩
      Ci • S h • X • CX                    ≈⟨ back _ (trans (sym assoc) (trans (front _ (Sᶠ-X 1F)) assoc)) ⟩
      Ci • X • (Z h₁ • S h) • CX           ≈⟨ trans (sym assoc) (front _ (Pow.pow-comm (₂₊ n) (toℕ (- 1F)) CX-X)) ⟩
      (X • Ci) • (Z h₁ • S h) • CX         ≈⟨ by-passoc ((□ • □) • (□ • □) • □) (□ • □ • □ • □ • □) Eq.refl ⟩
      X • Ci • Z h₁ • S h • CX             ≈⟨ back _ (back _ (back _ (sym (cancel-in (CX-invʳ 1F) _)))) ⟩
      X • Ci • Z h₁ • CX • Ci • S h • CX   ≈⟨ back _ (by-passoc (□ • □ • □ • □ • □ • □) ((□ • □ • □) • □ • □ • □) Eq.refl) ⟩
      X • (Ci • Z h₁ • CX) • Ci • S h • CX ≈⟨ back _ (front _ CZ₀-conj) ⟩
      X • (Z h₁ • Z h₁ ↑) • P              ≈⟨ back _ assoc ⟩
      X • Z h₁ • Z h₁ ↑ • P                ∎

  CZ-X : (₂₊ n) ⊢ CZ h • X ≈ X • CZ h • Z h₁ ↑
  CZ-X = begin
    (Si₀ • Si₁ • P) • X                            ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • □ • □) Eq.refl ⟩
    Si₀ • Si₁ • P • X                              ≈⟨ back _ (back _ P-X) ⟩
    Si₀ • Si₁ • X • Z h₁ • Z h₁ ↑ • P              ≈⟨ back _ (trans (sym assoc) (trans (front _ Si₁-X) assoc)) ⟩
    Si₀ • X • Si₁ • Z h₁ • Z h₁ ↑ • P              ≈⟨ trans (sym assoc) (trans (front _ (Sᶠ-X (- 1F))) assoc) ⟩
    X • (Z h₁ ^ᶠ (- 1F) • Si₀) • Si₁ • Z h₁ • Z h₁ ↑ • P
      ≈⟨ back _ (trans assoc (back _ (back _ (trans (sym assoc) (trans (front _ (sym Z∥Si₁)) assoc))))) ⟩
    X • Z h₁ ^ᶠ (- 1F) • Si₀ • Z h₁ • Si₁ • Z h₁ ↑ • P
      ≈⟨ back _ (back _ (trans (sym assoc) (trans (front _ (Sᶠ∥Zᶠ (- 1F) 1F)) assoc))) ⟩
    X • Z h₁ ^ᶠ (- 1F) • Z h₁ • Si₀ • Si₁ • Z h₁ ↑ • P
      ≈⟨ back _ (trans (sym assoc) (trans (front _ (OZ.^ᶠ-inverseˡ 1F)) left-unit)) ⟩
    X • Si₀ • Si₁ • Z h₁ ↑ • P
      ≈⟨ back _ (back _ (back _ Z↑∥P)) ⟩
    X • Si₀ • Si₁ • P • Z h₁ ↑
      ≈⟨ back _ (by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl) ⟩
    X • (Si₀ • Si₁ • P) • Z h₁ ↑ ∎
    where
    module OZ = Pow.Order (₂₊ n) {Z h₁} Z-order
    Si₁-X : (₂₊ n) ⊢ Si₁ • X ≈ X • Si₁
    Si₁-X = comm-gate₁-w↑ X-gate (S h ^ᶠ (- 1F))
    Z∥Si₁ : (₂₊ n) ⊢ Z h₁ ∥ Si₁
    Z∥Si₁ = Zᶠ-up 1F (S h ^ᶠ (- 1F))
