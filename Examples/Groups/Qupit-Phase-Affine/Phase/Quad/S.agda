------------------------------------------------------------------------
-- Presentations of groups
--
-- Quadratic phases: S, and the phase gadget it makes with CX
--
-- From level 2 on there is S, of order p (rule (24)), commuting with
-- Z (rule (26)).  It moves past the affine generators by substituting
-- into its phase (x₀ choose 2): a multiplier scales it into S and Z
-- (rule (27)), X shifts it into S and Z (rule (25)), and on the control
-- of CX it commutes with it (rule (29)), hence also on the control of
-- CXʳ.  So S is a one-wire gate of Phase.Gadget, and
--
--     P = CX⁻¹ • S • CX                   (S on x₀ + x₁)
--
-- is also CXʳ⁻¹ • S ↑ • CXʳ (P≈P′).  Read either way, P commutes with S
-- and Z on both wires, which is what makes CZ = S⁻¹ • S⁻¹ ↑ • P a
-- product of commuting diagonal gates (Phase.Quad.CZ).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Phase.Quad.S
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) (h : 2 ≤ lv) where

open import Data.Fin.Base using (toℕ)
open import Data.Nat.Base using (zero ; suc)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_ ; _^_)

open import Notations using (₁₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
  using (F ; F* ; p ; 0F ; 1F ; _+_ ; _*_ ; -_ ; -1* ; binom2 ; module FR)
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Powers p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Lib p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Wires p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Fan p-2 p-prime lv using (conjᶠ)
open import Examples.Groups.Qupit-Phase-Affine.Phase.Gadget p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Commute p-2 p-prime lv public
open import Examples.Groups.Qupit-Phase-Affine.Phase.Linear p-2 p-prime lv (lin₂ h) public

private
  variable
    n : ℕ

  h₁ : 1 ≤ lv
  h₁ = lin₂ h

------------------------------------------------------------------------
-- S on one wire

module _ {n : ℕ} where

  open Width (₁₊ n)

  S-order : (₁₊ n) ⊢ S h ^ p ≈ ε
  S-order = ax (ax24 h)

  private
    module OS = Pow.Order (₁₊ n) {S h} S-order
    module OZ = Pow.Order (₁₊ n) {Z h₁} Z-order

  -- Rule (26).
  S∥Z : (₁₊ n) ⊢ S h ∥ Z h₁
  S∥Z = ax (ax26 h)

  Sᶠ∥Zᶠ : (d c : F) → (₁₊ n) ⊢ (S h ^ᶠ d) ∥ (Z h₁ ^ᶠ c)
  Sᶠ∥Zᶠ d c = ∥-^ᶠ² d c S∥Z

  -- On wire 0, S commutes with everything one wire up.
  Sᶠ-up : (d : F) (w : Circuit n) → (₁₊ n) ⊢ (S h ^ᶠ d) ∥ (w ↑)
  Sᶠ-up d w = ∥-^ᶠ d (sym (comm-gate₁-w↑ (S-gate h) w))

  -- Rule (27): a multiplier scales S.
  Sᶠ-M : (d : F) (x : F*) →
         (₁₊ n) ⊢ S h ^ᶠ d • M⟨ x ⟩ ≈ M⟨ x ⟩ • Z h₁ ^ᶠ (d * binom2 (proj₁ x)) • S h ^ᶠ (d * (proj₁ x * proj₁ x))
  Sᶠ-M d x = begin
    S h ^ᶠ d • M⟨ x ⟩                          ≈⟨ slideʳᶠ d (ax (ax27 h x)) ⟩
    M⟨ x ⟩ • (Z h₁ ^ᶠ b • S h ^ᶠ s) ^ᶠ d       ≈⟨ back _ (Pow.pow-• (₁₊ n) (toℕ d) (∥-sym (Sᶠ∥Zᶠ s b))) ⟩
    M⟨ x ⟩ • (Z h₁ ^ᶠ b) ^ᶠ d • (S h ^ᶠ s) ^ᶠ d
      ≈⟨ back _ (cong (trans (OZ.^ᶠ-* b d) (OZ.^ᶠ-≡ (FR.*-comm b d))) (trans (OS.^ᶠ-* s d) (OS.^ᶠ-≡ (FR.*-comm s d)))) ⟩
    M⟨ x ⟩ • Z h₁ ^ᶠ (d * b) • S h ^ᶠ (d * s) ∎
    where
    b = binom2 (proj₁ x)
    s = proj₁ x * proj₁ x
    slideʳᶠ : ∀ {g a c : Circuit (₁₊ n)} (k : F) → (₁₊ n) ⊢ a • g ≈ g • c → (₁₊ n) ⊢ a ^ᶠ k • g ≈ g • c ^ᶠ k
    slideʳᶠ k e = sym (slideᶠ k (sym e))

  -- Rule (25): X shifts S.
  Sᶠ-X : (d : F) → (₁₊ n) ⊢ S h ^ᶠ d • X ≈ X • Z h₁ ^ᶠ d • S h ^ᶠ d
  Sᶠ-X d = begin
    S h ^ᶠ d • X                     ≈⟨ sym (slideᶠ d (sym (ax (ax25 h)))) ⟩
    X • (Z h₁ • S h) ^ᶠ d            ≈⟨ back _ (Pow.pow-• (₁₊ n) (toℕ d) (sym S∥Z)) ⟩
    X • Z h₁ ^ᶠ d • S h ^ᶠ d         ∎

------------------------------------------------------------------------
-- S and the two-wire gates

module _ {n : ℕ} where

  open Width (₂₊ n)

  private
    ss : (₂₊ n) ⊢ SWAP • SWAP ≈ ε
    ss = ax swap-order

  -- Rule (29): S on the control of CX.
  S↑-CX : (₂₊ n) ⊢ CX • S h ↑ ≈ S h ↑ • CX
  S↑-CX = ax (ax29 h)

  -- SWAP moves S a wire.
  sS : (₂₊ n) ⊢ SWAP • S h ≈ S h ↑ • SWAP
  sS = unslide ss (sym (ax (swap-S h)))

  sS↑ : (₂₊ n) ⊢ SWAP • S h ↑ ≈ S h • SWAP
  sS↑ = sym (ax (swap-S h))

  sSᶠ : (d : F) → (₂₊ n) ⊢ SWAP • S h ^ᶠ d ≈ (S h ^ᶠ d) ↑ • SWAP
  sSᶠ d = trans (slideᶠ d sS) (front _ (refl' (Eq.sym (↑ᶠ (S h) d))))

  sS↑ᶠ : (d : F) → (₂₊ n) ⊢ SWAP • (S h ^ᶠ d) ↑ ≈ S h ^ᶠ d • SWAP
  sS↑ᶠ d = trans (back _ (refl' (↑ᶠ (S h) d))) (slideᶠ d sS↑)

  -- On the control of CXʳ, by SWAP.
  S∥CXʳ : (₂₊ n) ⊢ S h • CXʳ ≈ CXʳ • S h
  S∥CXʳ = across (slide sS↑ sCX) (slide sCX sS↑) (sym S↑-CX)

  Z∥CXʳ : (₂₊ n) ⊢ Z h₁ • CXʳ ≈ CXʳ • Z h₁
  Z∥CXʳ = across (slide sZ↑ sCX) (slide sCX sZ↑) (sym Z↑-CX)
    where
    sZ↑ : (₂₊ n) ⊢ SWAP • Z h₁ ↑ ≈ Z h₁ • SWAP
    sZ↑ = sym (ax (swap-Z h₁))

  -- The gadget: S on x₀ + x₁, with either wire as target.
  P : Circuit (₂₊ n)
  P = CX ^ᶠ (- 1F) • S h • CX

  P′ : Circuit (₂₊ n)
  P′ = CXʳ ^ᶠ (- 1F) • S h ↑ • CXʳ

  P≈P′ : (₂₊ n) ⊢ P ≈ P′
  P≈P′ = begin
    CX ^ᶠ (- 1F) • S h • CX           ≈⟨ back _ (gadget S∥CXʳ (sym (comm-gate₁-w↑ (S-gate h) M⟨ -1* ⟩)) (ax (swap-S h))) ⟩
    CX ^ᶠ (- 1F) • CX • P′            ≈⟨ cancel-in (CX-invˡ 1F) _ ⟩
    P′                                ∎

  -- P's iterates are the gadgets of S's iterates.
  P^ : (k : ℕ) → (₂₊ n) ⊢ P ^ k ≈ CX ^ᶠ (- 1F) • S h ^ k • CX
  P^ = conj-pow (CX-invˡ 1F) (CX-invʳ 1F)

  -- P commutes with S and Z on both wires.
  S∥S↑ : (₂₊ n) ⊢ S h ∥ S h ↑
  S∥S↑ = sym (comm-gate₁-w↑ (S-gate h) (S h))

  S∥P : (₂₊ n) ⊢ S h ∥ P
  S∥P = trans (back _ P≈P′) (trans S∥P′ (front _ (sym P≈P′)))
    where
    S∥P′ : (₂₊ n) ⊢ S h ∥ P′
    S∥P′ = ∥-• (∥-sym (∥-^ᶠ (- 1F) (∥-sym S∥CXʳ))) (∥-• S∥S↑ S∥CXʳ)

  S↑∥P : (₂₊ n) ⊢ S h ↑ ∥ P
  S↑∥P = ∥-• (∥-sym (∥-^ᶠ (- 1F) (∥-sym S↑-CX′))) (∥-• (∥-sym S∥S↑) S↑-CX′)
    where
    S↑-CX′ : (₂₊ n) ⊢ S h ↑ ∥ CX
    S↑-CX′ = sym S↑-CX

  Z∥P : (₂₊ n) ⊢ Z h₁ ∥ P
  Z∥P = trans (back _ P≈P′) (trans Z∥P′ (front _ (sym P≈P′)))
    where
    Z∥S↑ : (₂₊ n) ⊢ Z h₁ ∥ S h ↑
    Z∥S↑ = sym (comm-gate₁-w↑ (Z-gate h₁) (S h))
    Z∥P′ : (₂₊ n) ⊢ Z h₁ ∥ P′
    Z∥P′ = ∥-• (∥-sym (∥-^ᶠ (- 1F) (∥-sym Z∥CXʳ))) (∥-• Z∥S↑ Z∥CXʳ)

  Z↑∥P : (₂₊ n) ⊢ Z h₁ ↑ ∥ P
  Z↑∥P = ∥-• (∥-sym (∥-^ᶠ (- 1F) (∥-sym Z↑∥CX))) (∥-• Z↑∥S Z↑∥CX)
    where
    Z↑∥CX : (₂₊ n) ⊢ Z h₁ ↑ ∥ CX
    Z↑∥CX = sym Z↑-CX
    Z↑∥S : (₂₊ n) ⊢ Z h₁ ↑ ∥ S h
    Z↑∥S = comm-gate₁-w↑ (S-gate h) (Z h₁)
