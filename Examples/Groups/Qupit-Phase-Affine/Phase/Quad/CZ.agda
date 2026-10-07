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
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) (h : 2 ≤ lv) (odd : 1 ≤ p-2) where

import Data.Integer.Base as ℤ
open import Data.Fin.Base using (toℕ)
open import Data.Nat.Base using (zero ; suc)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_ ; _^_)

open import Notations using (₁₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
  using ( F ; F* ; p ; 0F ; 1F ; 2F ; _+_ ; _*_ ; -_ ; -1* ; binom2 ; half ; module FR ; module Odd
        ; solve ; _:+_ ; _:*_ ; :-_ ; _:-_ ; _:=_ ; con )
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

------------------------------------------------------------------------
-- CZ past CX: conjugating by M₋₁ on the control

module _ {n : ℕ} where

  open Width (₂₊ n)

  private
    module OS = Pow.Order (₁₊ n) {S h} S-order
    module OS₂ = Pow.Order (₂₊ n) {S h} S-order
    module OZ = Pow.Order (₁₊ n) {Z h₁} Z-order
    module OCZ = Pow.Order (₂₊ n) {CZ h} CZ-order

    S₀ S₁ Z₁ Si₀ Si₁ Ci m CZi Pi S2₁ : Circuit (₂₊ n)
    S₀  = S h
    S₁  = S h ↑
    Z₁  = Z h₁ ↑
    Si₀ = S h ^ᶠ (- 1F)
    Si₁ = (S h ^ᶠ (- 1F)) ↑
    Ci  = CX ^ᶠ (- 1F)
    m   = M⟨ -1* ⟩ ↑
    CZi = CZ h ^ᶠ (- 1F)
    Pi  = P ^ᶠ (- 1F)
    S2₁ = (S h ^ᶠ 2F) ↑

    neg² : - 1F * - 1F ≡ 1F
    neg² = solve 0 ((:- con (ℤ.+ 1)) :* (:- con (ℤ.+ 1)) := con (ℤ.+ 1)) Eq.refl

    binom2-1 : binom2 (- 1F) ≡ 1F
    binom2-1 = Eq.trans (Odd.binom2-neg odd 1F)
      (Eq.trans (Eq.cong (_+ 1F) (solve 1 (λ t → con (ℤ.+ 1) :* (con (ℤ.+ 1) :- con (ℤ.+ 1)) :* t := con (ℤ.+ 0))
                                           Eq.refl half))
                (FR.+-identityˡ 1F))

    mm : (₂₊ n) ⊢ m • m ≈ ε
    mm = lift (Width.trans (ax (ax2 -1* -1*)) (Width.trans (Width.refl' (₁₊ n) (M-≡ neg²)) (ax ax1)))

    -- Rule (4) at -1, and its readings.
    Cm : (₂₊ n) ⊢ CX • m ≈ m • Ci
    Cm = ax (ax4 -1*)

    mCm : (₂₊ n) ⊢ m • CX • m ≈ Ci
    mCm = trans (back _ Cm) (cancel-in mm _)

    mCi : (₂₊ n) ⊢ m • Ci ≈ CX • m
    mCi = trans (back _ (sym mCm)) (cancel-in mm _)

    mC : (₂₊ n) ⊢ m • CX ≈ Ci • m
    mC = trans (sym (cancel-at mm _)) (trans (by-passoc ((□ • □) • □ • □) ((□ • □ • □) • □) Eq.refl) (front _ mCm))

    mCim : (₂₊ n) ⊢ m • Ci • m ≈ CX
    mCim = trans (sym assoc) (trans (front _ mCi) (trans assoc (cancel-at mm _)))

    -- Rule (27) at -1 on wire 1: S ↑ m = m Z ↑ S ↑.
    S₁m : (₂₊ n) ⊢ S₁ • m ≈ m • Z₁ • S₁
    S₁m = lift (Width.trans (ax (ax27 h -1*))
                 (Width.back (₁₊ n) _ (Width.cong (OZ.^ᶠ-≡ binom2-1) (OS.^ᶠ-≡ neg²))))

    m∥S₀ : (₂₊ n) ⊢ m ∥ S₀
    m∥S₀ = comm-gate₁-w↑ (S-gate h) M⟨ -1* ⟩

    m∥Si₀ : (₂₊ n) ⊢ m ∥ Si₀
    m∥Si₀ = ∥-sym (∥-^ᶠ (- 1F) (∥-sym m∥S₀))

    mP : (₂₊ n) ⊢ m • P ≈ CX • S₀ • Ci • m
    mP = begin
      m • Ci • S₀ • CX          ≈⟨ trans (sym assoc) (trans (front _ mCi) assoc) ⟩
      CX • m • S₀ • CX          ≈⟨ back _ (trans (sym assoc) (trans (front _ m∥S₀) assoc)) ⟩
      CX • S₀ • m • CX          ≈⟨ back _ (back _ mC) ⟩
      CX • S₀ • Ci • m          ∎

    CiS₁ : (₂₊ n) ⊢ Ci • S₁ ≈ S₁ • Ci
    CiS₁ = Pow.pow-comm (₂₊ n) (toℕ (- 1F)) S↑-CX

    Pi≈ : (₂₊ n) ⊢ Pi ≈ Ci • Si₀ • CX
    Pi≈ = P^ (toℕ (- 1F))

    -- S^(-1)^(-1) = S, on either wire.
    Si-inv₁ : (₁₊ n) ⊢ (S h ^ᶠ (- 1F)) ^ᶠ (- 1F) ≈ S h
    Si-inv₁ = Width.trans (OS.^ᶠ-* (- 1F) (- 1F)) (OS.^ᶠ-≡ neg²)

    Si-inv₂ : (₂₊ n) ⊢ (S h ^ᶠ (- 1F)) ^ᶠ (- 1F) ≈ S h
    Si-inv₂ = trans (OS₂.^ᶠ-* (- 1F) (- 1F)) (OS₂.^ᶠ-≡ neg²)

    CZi≈ : (₂₊ n) ⊢ CZi ≈ S₀ • S₁ • Pi
    CZi≈ = trans (CZ^ (toℕ (- 1F)))
             (cong Si-inv₂ (cong (trans (refl' (Eq.sym (↑-pow (S h ^ᶠ (- 1F)) (toℕ (- 1F))))) (lift Si-inv₁))
                                 refl))

    S₁PiS₀ : (₂₊ n) ⊢ S₁ • Pi • S₀ ≈ CZi
    S₁PiS₀ = begin
      S₁ • Pi • S₀          ≈⟨ back _ (sym S₀∥Pi) ⟩
      S₁ • S₀ • Pi          ≈⟨ trans (sym assoc) (trans (front _ (sym S∥S↑)) assoc) ⟩
      S₀ • S₁ • Pi          ≈⟨ sym CZi≈ ⟩
      CZi                   ∎
      where
      S₀∥Pi : (₂₊ n) ⊢ S₀ ∥ Pi
      S₀∥Pi = ∥-sym (∥-^ᶠ (- 1F) (∥-sym S∥P))

    two-one : 2F + - 1F ≡ 1F
    two-one = solve 0 ((con (ℤ.+ 1) :+ con (ℤ.+ 1)) :+ (:- con (ℤ.+ 1)) := con (ℤ.+ 1)) Eq.refl

    step-a : (₂₊ n) ⊢ S2₁ • Z₁ • Si₀ • Si₁ • P ≈ Z₁ • S₁ • Si₀ • P
    step-a = begin
      S2₁ • Z₁ • Si₀ • Si₁ • P      ≈⟨ trans (sym assoc) (trans (front _ (lift (Sᶠ∥Zᶠ 2F 1F))) assoc) ⟩
      Z₁ • S2₁ • Si₀ • Si₁ • P      ≈⟨ back _ (trans (sym assoc) (trans (front _ (sym (Sᶠ-up (- 1F) (S h ^ᶠ 2F)))) assoc)) ⟩
      Z₁ • Si₀ • S2₁ • Si₁ • P      ≈⟨ back _ (back _ (trans (sym assoc) (front _ merge))) ⟩
      Z₁ • Si₀ • S₁ • P             ≈⟨ back _ (trans (sym assoc) (trans (front _ (Sᶠ-up (- 1F) (S h))) assoc)) ⟩
      Z₁ • S₁ • Si₀ • P             ∎
      where
      merge : (₂₊ n) ⊢ S2₁ • Si₁ ≈ S₁
      merge = lift (Width.trans (OS.^ᶠ-+ 2F (- 1F)) (OS.^ᶠ-≡ two-one))

  CZ-CX : (₂₊ n) ⊢ CZ h • CX ≈ CX • (S h ^ᶠ 2F) ↑ • Z h₁ ↑ • CZ h
  CZ-CX = sym (begin
    CX • S2₁ • Z₁ • Si₀ • Si₁ • P
      ≈⟨ back _ step-a ⟩
    CX • Z₁ • S₁ • Si₀ • P
      ≈⟨ back _ (sym (cancel-in mm _)) ⟩
    CX • m • m • Z₁ • S₁ • Si₀ • P
      ≈⟨ back _ (back _ (trans (by-passoc (□ • □ • □ • □ • □) ((□ • □ • □) • □ • □) Eq.refl)
                                 (front _ (sym S₁m)))) ⟩
    CX • m • (S₁ • m) • Si₀ • P
      ≈⟨ back _ (back _ (trans assoc (back _ (trans (sym assoc) (trans (front _ m∥Si₀) assoc))))) ⟩
    CX • m • S₁ • Si₀ • m • P
      ≈⟨ back _ (back _ (back _ (back _ mP))) ⟩
    CX • m • S₁ • Si₀ • CX • S₀ • Ci • m
      ≈⟨ trans (sym assoc) (trans (front _ Cm) assoc) ⟩
    m • Ci • S₁ • Si₀ • CX • S₀ • Ci • m
      ≈⟨ back _ (trans (sym assoc) (trans (front _ CiS₁) assoc)) ⟩
    m • S₁ • Ci • Si₀ • CX • S₀ • Ci • m
      ≈⟨ back _ (back _ (by-passoc (□ • □ • □ • □ • □ • □) ((□ • □ • □) • □ • □ • □) Eq.refl)) ⟩
    m • S₁ • (Ci • Si₀ • CX) • S₀ • Ci • m
      ≈⟨ back _ (back _ (front _ (sym Pi≈))) ⟩
    m • S₁ • Pi • S₀ • Ci • m
      ≈⟨ back _ (trans (by-passoc (□ • □ • □ • □ • □) ((□ • □ • □) • □ • □) Eq.refl) (front _ S₁PiS₀)) ⟩
    m • CZi • Ci • m
      ≈⟨ back _ (back _ (sym (cancel-in mm _))) ⟩
    m • CZi • m • m • Ci • m
      ≈⟨ by-passoc (□ • □ • □ • □ • □ • □) ((□ • □ • □) • (□ • □ • □)) Eq.refl ⟩
    (m • CZi • m) • (m • Ci • m)
      ≈⟨ cong (ax (ax28 h)) mCim ⟩
    CZ h • CX ∎)
