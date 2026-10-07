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
--   S-conj   CX⁻ᶜ S CXᶜ = S (Sᶜ² Zᵇ⁽ᶜ⁾) ↑ CZᶜ, b the binomial coefficient
--            (c 2), by induction from CZ-CX (the paper's CZ-S-gadget);
--   CZ-M₁    a multiplier on wire 1 scales it (the paper's CZ-M), by
--            moving it through S-conj; CZ-M₀ on wire 0, by symmetry.
--
-- SZ q b = S^q Z^b collects the one-wire diagonal words the gadget
-- leaves behind.
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
  using ( F ; F* ; p ; 0F ; 1F ; 2F ; _+_ ; _-_ ; _*_ ; -_ ; -1* ; binom2 ; half ; _×ᶠ_ ; ×ᶠ-toℕ
        ; module FR ; module Odd ; solve ; _:+_ ; _:*_ ; :-_ ; _:-_ ; _:=_ ; con )
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Powers p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Lib p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Wires p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Fan p-2 p-prime lv using (conjᶠ)
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

------------------------------------------------------------------------
-- S and Z on one wire, as one word

module _ {n : ℕ} where

  open Width (₁₊ n)

  private
    module OS = Pow.Order (₁₊ n) {S h} S-order
    module OZ = Pow.Order (₁₊ n) {Z h₁} Z-order

  SZ : F → F → Circuit (₁₊ n)
  SZ q b = S h ^ᶠ q • Z h₁ ^ᶠ b

  SZ-≡ : {q b q' b' : F} → q ≡ q' → b ≡ b' → (₁₊ n) ⊢ SZ q b ≈ SZ q' b'
  SZ-≡ Eq.refl Eq.refl = refl

  SZ-zero : (₁₊ n) ⊢ SZ 0F 0F ≈ ε
  SZ-zero = left-unit

  SZ-add : (q b q' b' : F) → (₁₊ n) ⊢ SZ q b • SZ q' b' ≈ SZ (q + q') (b + b')
  SZ-add q b q' b' = begin
    (S h ^ᶠ q • Z h₁ ^ᶠ b) • S h ^ᶠ q' • Z h₁ ^ᶠ b'
      ≈⟨ by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
    S h ^ᶠ q • (Z h₁ ^ᶠ b • S h ^ᶠ q') • Z h₁ ^ᶠ b'
      ≈⟨ back _ (front _ (sym (Sᶠ∥Zᶠ q' b))) ⟩
    S h ^ᶠ q • (S h ^ᶠ q' • Z h₁ ^ᶠ b) • Z h₁ ^ᶠ b'
      ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
    (S h ^ᶠ q • S h ^ᶠ q') • Z h₁ ^ᶠ b • Z h₁ ^ᶠ b'
      ≈⟨ cong (OS.^ᶠ-+ q q') (OZ.^ᶠ-+ b b') ⟩
    S h ^ᶠ (q + q') • Z h₁ ^ᶠ (b + b') ∎

  SZ-^ᶠ : (q b c : F) → (₁₊ n) ⊢ SZ q b ^ᶠ c ≈ SZ (q * c) (b * c)
  SZ-^ᶠ q b c = trans (Pow.pow-• (₁₊ n) (toℕ c) (Sᶠ∥Zᶠ q b)) (cong (OS.^ᶠ-* q c) (OZ.^ᶠ-* b c))

  -- The inverse.
  SZ-inv : (q b : F) → (₁₊ n) ⊢ SZ (- q) (- b) • SZ q b ≈ ε
  SZ-inv q b = trans (SZ-add (- q) (- b) q b)
                 (trans (SZ-≡ (FR.-‿inverseˡ q) (FR.-‿inverseˡ b)) SZ-zero)

  -- The inverse written as rule (27) at -1 leaves it.
  SZ-cancel : (q b : F) → (₁₊ n) ⊢ (Z h₁ ^ᶠ (- 1F * b) • S h ^ᶠ (- 1F * q)) • SZ q b ≈ ε
  SZ-cancel q b = begin
    (Z h₁ ^ᶠ (- 1F * b) • S h ^ᶠ (- 1F * q)) • SZ q b
      ≈⟨ front _ (sym (Sᶠ∥Zᶠ (- 1F * q) (- 1F * b))) ⟩
    SZ (- 1F * q) (- 1F * b) • SZ q b
      ≈⟨ front _ (SZ-≡ (negs q) (negs b)) ⟩
    SZ (- q) (- b) • SZ q b
      ≈⟨ SZ-inv q b ⟩
    ε ∎
    where
    negs : ∀ t → - 1F * t ≡ - t
    negs = solve 1 (λ t → (:- con (ℤ.+ 1)) :* t := :- t) Eq.refl

------------------------------------------------------------------------
-- The S gadget with any weight, and CZ under a multiplier

module _ {n : ℕ} where

  open Width (₂₊ n)

  private
    module OS₁ = Pow.Order (₁₊ n) {S h} S-order
    module OS₂ = Pow.Order (₂₊ n) {S h} S-order
    module OCZ = Pow.Order (₂₊ n) {CZ h} CZ-order

    Si₀ Si₁ Ci : Circuit (₂₊ n)
    Si₀ = S h ^ᶠ (- 1F)
    Si₁ = (S h ^ᶠ (- 1F)) ↑
    Ci  = CX ^ᶠ (- 1F)

    up-iter′ : (w : Circuit (₁₊ n)) {y : Circuit (₂₊ n)} (k : F) → (₂₊ n) ⊢ w ↑ ∥ y → (₂₊ n) ⊢ (w ^ᶠ k) ↑ ∥ y
    up-iter′ w k e = trans (front _ (refl' (↑ᶠ w k)))
                       (trans (∥-^ᶠ k e) (back _ (refl' (Eq.sym (↑ᶠ w k)))))

    SZ↑∥ : {y : Circuit (₂₊ n)} (q b : F) → (₂₊ n) ⊢ S h ↑ ∥ y → (₂₊ n) ⊢ Z h₁ ↑ ∥ y →
           (₂₊ n) ⊢ SZ q b ↑ ∥ y
    SZ↑∥ q b es ez = •-∥ (up-iter′ (S h) q es) (up-iter′ (Z h₁) b ez)

  SZ↑∥CX : (q b : F) → (₂₊ n) ⊢ SZ q b ↑ ∥ CX
  SZ↑∥CX q b = SZ↑∥ q b (sym S↑-CX) (sym Z↑-CX)

  SZ↑∥CZ : (q b : F) → (₂₊ n) ⊢ SZ q b ↑ ∥ CZ h
  SZ↑∥CZ q b = SZ↑∥ q b S↑∥CZ Z↑∥CZ

  SZ↑∥S : (q b : F) → (₂₊ n) ⊢ SZ q b ↑ ∥ S h
  SZ↑∥S q b = comm-gate₁-w↑ (S-gate h) (SZ q b)

  -- P is S on both wires times CZ.
  P-SZ : (₂₊ n) ⊢ P ≈ S h • SZ 1F 0F ↑ • CZ h
  P-SZ = sym (begin
    S h • SZ 1F 0F ↑ • Si₀ • Si₁ • P      ≈⟨ back _ (front _ right-unit) ⟩
    S h • S h ↑ • Si₀ • Si₁ • P            ≈⟨ back _ (trans (sym assoc) (trans (front _ (sym (Sᶠ-up (- 1F) (S h)))) assoc)) ⟩
    S h • Si₀ • S h ↑ • Si₁ • P            ≈⟨ trans (sym assoc) (front _ OS₂.inverseʳ) ⟩
    ε • S h ↑ • Si₁ • P                    ≈⟨ trans left-unit (trans (sym assoc) (trans (front _ (lift OS₁.inverseʳ)) left-unit)) ⟩
    P                                      ∎)

  -- S past CX: the gadget of weight 1.
  S-CX : (₂₊ n) ⊢ S h • CX ≈ CX • S h • SZ 1F 0F ↑ • CZ h
  S-CX = begin
    S h • CX                      ≈⟨ sym left-unit ⟩
    ε • S h • CX                  ≈⟨ front _ (sym (CX-invʳ 1F)) ⟩
    (CX • Ci) • S h • CX          ≈⟨ assoc ⟩
    CX • P                        ≈⟨ back _ P-SZ ⟩
    CX • S h • SZ 1F 0F ↑ • CZ h  ∎

  -- CZ past an iterate of CX.
  CZ-CXᶠ : (c : F) → (₂₊ n) ⊢ CZ h ^ᶠ c • CX ≈ CX • SZ (2F * c) c ↑ • CZ h ^ᶠ c
  CZ-CXᶠ c = begin
    CZ h ^ᶠ c • CX                         ≈⟨ sym (slide^ (toℕ c) (sym (trans CZ-CX (back _ (sym assoc))))) ⟩
    CX • (SZ 2F 1F ↑ • CZ h) ^ᶠ c          ≈⟨ back _ (Pow.pow-• (₂₊ n) (toℕ c) (SZ↑∥CZ 2F 1F)) ⟩
    CX • (SZ 2F 1F ↑) ^ᶠ c • CZ h ^ᶠ c     ≈⟨ back _ (front _ (trans (refl' (Eq.sym (↑ᶠ (SZ 2F 1F) c)))
                                                 (lift (Width.trans (SZ-^ᶠ 2F 1F c) (SZ-≡ Eq.refl (FR.*-identityˡ c)))))) ⟩
    CX • SZ (2F * c) c ↑ • CZ h ^ᶠ c       ∎

  -- The S gadget of weight m, by induction.
  private
    ĉ : ℕ → F
    ĉ m = m ×ᶠ 1F

    CX-split : (m : ℕ) → (₂₊ n) ⊢ CX ^ suc m ≈ CX ^ m • CX
    CX-split m = trans (refl' (Eq.cong (CX ^_) (ℕP.+-comm 1 m))) (Pow.pow-+ (₂₊ n) CX m 1)

    sq-step : (c : F) → (1F + c * c) + 2F * c ≡ (1F + c) * (1F + c)
    sq-step = solve 1 (λ c → (con (ℤ.+ 1) :+ c :* c) :+ (con (ℤ.+ 1) :+ con (ℤ.+ 1)) :* c
                             := (con (ℤ.+ 1) :+ c) :* (con (ℤ.+ 1) :+ c)) Eq.refl

    b-step : (c : F) → (0F + binom2 c) + c ≡ binom2 (1F + c)
    b-step c = Eq.trans (Eq.cong (_+ c) (FR.+-identityˡ (binom2 c)))
                 (Eq.trans (Eq.sym (Odd.binom2-shift odd c)) (Eq.cong binom2 (FR.+-comm c 1F)))

    zero² : 0F * 0F ≡ 0F
    zero² = FR.zeroʳ 0F

    binom2-0 : binom2 0F ≡ 0F
    binom2-0 = Eq.trans (Eq.cong (_* half) (FR.zeroˡ (0F - 1F))) (FR.zeroˡ half)

  S-gad^ : (m : ℕ) → (₂₊ n) ⊢ S h • CX ^ m ≈ CX ^ m • S h • SZ (ĉ m * ĉ m) (binom2 (ĉ m)) ↑ • CZ h ^ᶠ ĉ m
  S-gad^ zero = sym (trans left-unit (back _ (trans (front _ (lift (Width.trans (SZ-≡ zero² binom2-0) SZ-zero))) left-unit)))
  S-gad^ (suc m) = begin
    S h • CX ^ suc m
      ≈⟨ back _ (CX-split m) ⟩
    S h • CX ^ m • CX
      ≈⟨ trans (sym assoc) (front _ (S-gad^ m)) ⟩
    (CX ^ m • S h • U q b • CZ h ^ᶠ c) • CX
      ≈⟨ by-passoc ((□ • □ • □ • □) • □) (□ • □ • □ • □ • □) Eq.refl ⟩
    CX ^ m • S h • U q b • CZ h ^ᶠ c • CX
      ≈⟨ back _ (back _ (back _ (CZ-CXᶠ c))) ⟩
    CX ^ m • S h • U q b • CX • U (2F * c) c • CZ h ^ᶠ c
      ≈⟨ back _ (back _ (trans (sym assoc) (trans (front _ (SZ↑∥CX q b)) assoc))) ⟩
    CX ^ m • S h • CX • U q b • U (2F * c) c • CZ h ^ᶠ c
      ≈⟨ back _ (trans (sym assoc) (trans (front _ S-CX) assoc)) ⟩
    CX ^ m • CX • (S h • U 1F 0F • CZ h) • U q b • U (2F * c) c • CZ h ^ᶠ c
      ≈⟨ back _ (back _ (by-passoc ((□ • □ • □) • □ • □ • □) (□ • □ • □ • □ • □ • □) Eq.refl)) ⟩
    CX ^ m • CX • S h • U 1F 0F • CZ h • U q b • U (2F * c) c • CZ h ^ᶠ c
      ≈⟨ back _ (back _ (back _ (back _ (trans (sym assoc) (trans (front _ (sym (SZ↑∥CZ q b))) assoc))))) ⟩
    CX ^ m • CX • S h • U 1F 0F • U q b • CZ h • U (2F * c) c • CZ h ^ᶠ c
      ≈⟨ back _ (back _ (back _ (back _ (back _ (trans (sym assoc) (trans (front _ (sym (SZ↑∥CZ (2F * c) c))) assoc)))))) ⟩
    CX ^ m • CX • S h • U 1F 0F • U q b • U (2F * c) c • CZ h • CZ h ^ᶠ c
      ≈⟨ back _ (back _ (back _ (trans (sym assoc) (front _ (lift (SZ-add 1F 0F q b)))))) ⟩
    CX ^ m • CX • S h • U (1F + q) (0F + b) • U (2F * c) c • CZ h • CZ h ^ᶠ c
      ≈⟨ back _ (back _ (back _ (trans (sym assoc) (front _ (lift (SZ-add (1F + q) (0F + b) (2F * c) c)))))) ⟩
    CX ^ m • CX • S h • U ((1F + q) + 2F * c) ((0F + b) + c) • CZ h • CZ h ^ᶠ c
      ≈⟨ back _ (back _ (back _ (cong (lift (SZ-≡ (sq-step c) (b-step c))) (OCZ.^ᶠ-+ 1F c)))) ⟩
    CX ^ m • CX • S h • U (c' * c') (binom2 c') • CZ h ^ᶠ c'
      ≈⟨ trans (sym assoc) (front _ (sym (CX-split m))) ⟩
    CX ^ suc m • S h • U (c' * c') (binom2 c') • CZ h ^ᶠ c' ∎
    where
    U : F → F → Circuit (₂₊ n)
    U q b = SZ q b ↑
    c c' q b : F
    c  = ĉ m
    c' = 1F + c
    q  = c * c
    b  = binom2 c

  S-gad : (c : F) → (₂₊ n) ⊢ S h • CX ^ᶠ c ≈ CX ^ᶠ c • S h • SZ (c * c) (binom2 c) ↑ • CZ h ^ᶠ c
  S-gad c = Eq.subst (λ t → (₂₊ n) ⊢ S h • CX ^ᶠ c ≈ CX ^ᶠ c • S h • SZ (t * t) (binom2 t) ↑ • CZ h ^ᶠ t)
                     (Eq.trans (×ᶠ-toℕ c 1F) (FR.*-identityʳ c)) (S-gad^ (toℕ c))

  -- The paper's CZ-S-gadget: S on x₀ + c x₁.
  S-conj : (c : F) → (₂₊ n) ⊢ CX ^ᶠ (- c) • S h • CX ^ᶠ c ≈ S h • SZ (c * c) (binom2 c) ↑ • CZ h ^ᶠ c
  S-conj c = trans (back _ (S-gad c)) (cancel-in (CX-invˡ c) _)

  -- A multiplier on wire 1 scales CZ (the paper's CZ-M).
  CZ-M₁ : (x : F*) → (₂₊ n) ⊢ CZ h • M⟨ x ⟩ ↑ ≈ M⟨ x ⟩ ↑ • CZ h ^ᶠ proj₁ x
  CZ-M₁ x = begin
    (Si₀ • Si₁ • Ci • S h • CX) • m
      ≈⟨ by-passoc ((□ • □ • □ • □ • □) • □) (□ • □ • □ • □ • □ • □) Eq.refl ⟩
    Si₀ • Si₁ • Ci • S h • CX • m
      ≈⟨ back _ (back _ (back _ (back _ (ax (ax4 x))))) ⟩
    Si₀ • Si₁ • Ci • S h • m • CX ^ᶠ a
      ≈⟨ back _ (back _ (back _ (trans (sym assoc) (trans (front _ (sym (comm-gate₁-w↑ (S-gate h) M⟨ x ⟩))) assoc)))) ⟩
    Si₀ • Si₁ • Ci • m • S h • CX ^ᶠ a
      ≈⟨ back _ (back _ (trans (sym assoc) (trans (front _ (CXᶠ-M↑ x (- 1F))) assoc))) ⟩
    Si₀ • Si₁ • m • CX ^ᶠ (- 1F * a) • S h • CX ^ᶠ a
      ≈⟨ back _ (trans (sym assoc) (trans (front _ (lift (Sᶠ-M (- 1F) x))) assoc)) ⟩
    Si₀ • m • W ↑ • CX ^ᶠ (- 1F * a) • S h • CX ^ᶠ a
      ≈⟨ trans (sym assoc) (trans (front _ (Sᶠ-up (- 1F) M⟨ x ⟩)) assoc) ⟩
    m • Si₀ • W ↑ • CX ^ᶠ (- 1F * a) • S h • CX ^ᶠ a
      ≈⟨ back _ (back _ (back _ (trans (front _ (CX-≡ neg1)) (S-conj a)))) ⟩
    m • Si₀ • W ↑ • S h • SZ s b ↑ • CZ h ^ᶠ a
      ≈⟨ back _ (back _ (trans (sym assoc) (trans (front _ (comm-gate₁-w↑ (S-gate h) W)) assoc))) ⟩
    m • Si₀ • S h • W ↑ • SZ s b ↑ • CZ h ^ᶠ a
      ≈⟨ back _ (trans (sym assoc) (trans (front _ OS₂.inverseˡ) left-unit)) ⟩
    m • W ↑ • SZ s b ↑ • CZ h ^ᶠ a
      ≈⟨ back _ (trans (sym assoc) (trans (front _ (lift W-cancel)) left-unit)) ⟩
    m • CZ h ^ᶠ a ∎
    where
    a s b : F
    a = proj₁ x
    s = a * a
    b = binom2 a
    m : Circuit (₂₊ n)
    m = M⟨ x ⟩ ↑
    W : Circuit (₁₊ n)
    W = Z h₁ ^ᶠ (- 1F * b) • S h ^ᶠ (- 1F * s)
    neg1 : - 1F * a ≡ - a
    neg1 = solve 1 (λ t → (:- con (ℤ.+ 1)) :* t := :- t) Eq.refl a
    W-cancel : (₁₊ n) ⊢ W • SZ s b ≈ ε
    W-cancel = SZ-cancel s b

  -- On wire 0, by the symmetry of CZ.
  CZ-M₀ : (x : F*) → (₂₊ n) ⊢ CZ h • M⟨ x ⟩ ≈ M⟨ x ⟩ • CZ h ^ᶠ proj₁ x
  CZ-M₀ x = begin
    CZ h • M⟨ x ⟩                          ≈⟨ front _ (sym (conjᶠ (ax swap-order) CZ-sym 1F)) ⟩
    (SWAP • CZ h • SWAP) • M⟨ x ⟩          ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • □ • □) Eq.refl ⟩
    SWAP • CZ h • SWAP • M⟨ x ⟩            ≈⟨ back _ (back _ (sM x)) ⟩
    SWAP • CZ h • M⟨ x ⟩ ↑ • SWAP          ≈⟨ back _ (trans (sym assoc) (trans (front _ (CZ-M₁ x)) assoc)) ⟩
    SWAP • M⟨ x ⟩ ↑ • CZ h ^ᶠ a • SWAP      ≈⟨ trans (sym assoc) (trans (front _ (sM↑ x)) assoc) ⟩
    M⟨ x ⟩ • SWAP • CZ h ^ᶠ a • SWAP       ≈⟨ back _ (conjᶠ (ax swap-order) CZ-sym a) ⟩
    M⟨ x ⟩ • CZ h ^ᶠ a                     ∎
    where
    a = proj₁ x
