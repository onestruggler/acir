------------------------------------------------------------------------
-- Presentations of groups
--
-- The semi-M↓CZ inj₂-inj₂ cases of srel-wd.  The key plumbing fact is
-- (M x) ↓ ≡ M x (the down-widening is letter-preserving, it only sticks
-- on the S-powers), after which the MD engine and the CZ^ engines drive
-- both sides to the axiom one width down.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (inj₁ ; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; _≢_)
open import Data.Fin using (Fin ; toℕ)
open import Data.Vec using ([] ; _∷_)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR
import Data.Nat.Properties as NP
open import Data.Nat.DivMod using (_%_)
open import Examples.Groups.Symplectic.CongDownK p-2 p-prime using (S^-↓ᵏ ; ↑↓ᵏ-comm)
import Data.Nat as Nat

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)
open Lemmas-Sym using (lemma-comm-S-w↑ ; lemma-comm-H-w↑ ; lemma-cong↑)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Algebra.Properties.Ring (+-*-ring p-2)
  using (-0#≈0# ; -‿distribʳ-*)

import Examples.Groups.Symplectic.BR.Three.DD-CZ p-2 p-prime as DDCZ
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDM p-2 p-prime
  using (nsum-* ; nsum-neg)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDZM p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDCZ p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMD p-2 p-prime

------------------------------------------------------------------------
-- The down-widening of an S-power (and hence of the M word) is the
-- same word one wire wider.

↓-pow-S : ∀ {n} (k : ℕ) → ((S ^ k) ↓) ≡ (S {₁₊ n} ^ k)
↓-pow-S zero          = Eq.refl
↓-pow-S (suc zero)    = Eq.refl
↓-pow-S (suc (suc k)) = Eq.cong (S •_) (↓-pow-S (suc k))

M↓≡ : ∀ {n} (x : ℤ* ₚ) → ((ZM x) ↓) ≡ ZM {₁₊ n} x
M↓≡ x = Eq.cong₂ _•_ (↓-pow-S (toℕ (x .proj₁)))
  (Eq.cong₂ _•_ Eq.refl
    (Eq.cong₂ _•_ (↓-pow-S (toℕ ((x ⁻¹) .proj₁)))
      (Eq.cong₂ _•_ Eq.refl
        (Eq.cong₂ _•_ (↓-pow-S (toℕ (x .proj₁))) Eq.refl))))

------------------------------------------------------------------------
-- semi-M↓CZ on a doubly-inj₂ coset, pattern (₀,·)/(₀,·): the D boxes
-- are CZ-transparent and the residual is the axiom itself.

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)

  private
    ract'' = ract {₂₊ m}

  semiMCZ-go-00 : ∀ (x : ℤ* ₚ) (b1 g2 b₂ : ℤ ₚ) (lm2 : C (₁₊ m)) →
    (x ⁻¹) .proj₁ * b1 ≡ b₂ →
    ((ract'' ᵗ) (inj₂ ((₀ , b1) , inj₂ ((₀ , g2) , lm2))) ((ZM x) ↓ • CZ)) ≋
    ((ract'' ᵗ) (inj₂ ((₀ , b1) , inj₂ ((₀ , g2) , lm2)))
      (CZ^ (x ^1) • (ZM x) ↓))
  semiMCZ-go-00 x b1 g2 b₂ lm2 eq₂ = resid≈ , coset≡
    where
    xv = x .proj₁
    lm : C (₂₊ m)
    lm = inj₂ ((₀ , g2) , lm2)

    c₂fix : ((ract'' ᵗ) (inj₂ ((₀ , b1) , lm)) (ZM x)) .proj₂ ≡
            inj₂ ((₀ , b₂) , lm)
    c₂fix = Eq.trans (MD-coset!0 x b1 lm)
              (Eq.cong (λ v → inj₂ ((₀ , v) , lm)) eq₂)

    -- CZ^ (x ^1) leaves a (₀,·)/(₀,·) box pair fixed.
    nz0 : nsum (toℕ xv) (- ₀) ≡ ₀
    nz0 = Eq.trans (nsum-neg xv ₀)
          (Eq.trans (Eq.cong -_ (*-zeroʳ xv)) -0#≈0#)

    cSfix : ((ract'' ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ ^ toℕ xv)) .proj₂ ≡
            inj₂ ((₀ , b1) , lm)
    cSfix = Eq.trans (ract-CZ^-coset (₀ , b1) (₀ , g2) lm2 (toℕ xv))
      (Eq.cong₂ (λ v w → inj₂ ((₀ , v) , inj₂ ((₀ , w) , lm2)))
        (Eq.trans (Eq.cong (b1 +_) nz0) (+-identityʳ b1))
        (Eq.trans (Eq.cong (g2 +_) nz0) (+-identityʳ g2)))

    resid≈ : ((ract'' ᵗ) (inj₂ ((₀ , b1) , lm)) ((ZM x) ↓ • CZ)) .proj₁ ≈
             ((ract'' ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ^ (x ^1) • (ZM x) ↓)) .proj₁
    resid≈ =
      trans (refl'ᵣ (Eq.cong (λ w → ((ract'' ᵗ) (inj₂ ((₀ , b1) , lm)) (w • CZ)) .proj₁)
              (M↓≡ x)))
      (trans (cong (MD-resid!0 x b1 lm)
        (refl'ᵣ (Eq.cong (λ c → ((ract'' ᵗ) c CZ) .proj₁) c₂fix)))
      (trans (refl'ᵣ (Eq.cong (_• CZ) (Eq.sym (M↓≡ x))))
      (trans (axiom (semi-M↓CZ x))
      (trans (refl'ᵣ (Eq.cong (CZ^ (x ^1) •_) (M↓≡ x)))
      (sym (trans (refl'ᵣ (Eq.cong (λ w → ((ract'' ᵗ) (inj₂ ((₀ , b1) , lm))
                     (CZ^ (x ^1) • w)) .proj₁) (M↓≡ x)))
           (trans (cong (ract-CZ^-resid (₀ , b1) (₀ , g2) lm2 (toℕ xv))
             (refl'ᵣ (Eq.cong (λ c → ((ract'' ᵗ) c (ZM x)) .proj₁) cSfix)))
           (cong refl (MD-resid!0 x b1 lm)))))))))

    coset≡ : ((ract'' ᵗ) (inj₂ ((₀ , b1) , lm)) ((ZM x) ↓ • CZ)) .proj₂ ≡
             ((ract'' ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ^ (x ^1) • (ZM x) ↓)) .proj₂
    coset≡ = Eq.trans
      (Eq.cong (λ w → ((ract'' ᵗ) (inj₂ ((₀ , b1) , lm)) (w • CZ)) .proj₂)
        (M↓≡ x))
      (Eq.trans (Eq.cong (λ c → ((ract'' ᵗ) c CZ) .proj₂) c₂fix)
      (Eq.trans
        (Eq.cong₂ (λ v w → inj₂ ((₀ , v) , inj₂ ((₀ , w) , lm2)))
          (Eq.trans (Eq.cong (b₂ +_) -0#≈0#) (+-identityʳ b₂))
          (Eq.trans (Eq.cong (g2 +_) -0#≈0#) (+-identityʳ g2)))
      (Eq.sym (Eq.trans
        (Eq.cong (λ w → ((ract'' ᵗ) (inj₂ ((₀ , b1) , lm))
            (CZ^ (x ^1) • w)) .proj₂) (M↓≡ x))
        (Eq.trans (Eq.cong (λ c → ((ract'' ᵗ) c (ZM x)) .proj₂) cSfix)
          c₂fix)))))

------------------------------------------------------------------------
-- Commutation of the bottom M word with lifted words, and the CZ slide.

  comm-up₂ : ∀ {u v : Word (Gen (₂₊ m))} (w : Word (Gen (₁₊ m))) →
    u • w ↑ ≈ w ↑ • u → v • w ↑ ≈ w ↑ • v →
    (u • v) • w ↑ ≈ w ↑ • (u • v)
  comm-up₂ w cu cv =
    trans assoc (trans (cong refl cv)
      (trans (sym assoc) (trans (cong cu refl) assoc)))

  comm-Spow-↑ : ∀ (j : ℕ) (w : Word (Gen (₁₊ m))) →
    (S ^ j) • w ↑ ≈ w ↑ • (S ^ j)
  comm-Spow-↑ j w = PP.comm⇒pow-comm ((₂₊ m) QRel,_===_)
    {w = S} {v = w ↑} j 1 (lemma-comm-S-w↑ w)

  comm-ZM-↑ : ∀ (x : ℤ* ₚ) (w : Word (Gen (₁₊ m))) →
    ZM x • w ↑ ≈ w ↑ • ZM x
  comm-ZM-↑ x w =
    comm-up₂ w (comm-Spow-↑ (toℕ (x .proj₁)) w)
      (comm-up₂ w (lemma-comm-H-w↑ w)
        (comm-up₂ w (comm-Spow-↑ (toℕ ((x ⁻¹) .proj₁)) w)
          (comm-up₂ w (lemma-comm-H-w↑ w)
            (comm-up₂ w (comm-Spow-↑ (toℕ (x .proj₁)) w)
              (lemma-comm-H-w↑ w)))))

  -- The residual-width instance of the axiom, in plain M-word form.
  MCZ-slide : ∀ (x : ℤ* ₚ) → ZM x • CZ ≈ CZ^ (x ^1) • ZM x
  MCZ-slide x =
    trans (refl'ᵣ (Eq.cong (_• CZ) (Eq.sym (M↓≡ x))))
    (trans (axiom (semi-M↓CZ x))
           (refl'ᵣ (Eq.cong (CZ^ (x ^1) •_) (M↓≡ x))))

  H↑3H↑≈ε : (H ↑) ^ 3 • H ↑ ≈ ε
  H↑3H↑≈ε = lemma-cong↑ (H ^ 3 • H) ε (H3H≈ε {m})

------------------------------------------------------------------------
-- Pattern (₀,·)/(₁₊ c2,·): the escape is the H↑-conjugated CZ; the M
-- word slides through the conjugation.

  semiMCZ-go-0c : ∀ (x : ℤ* ₚ) (xs' c2 : Fin (₁₊ p-2))
    (b1 g2 b₂ b₃ : ℤ ₚ) (lm2 : C (₁₊ m)) →
    x .proj₁ ≡ ₁₊ xs' →
    (x ⁻¹) .proj₁ * b1 ≡ b₂ →
    b1 + nsum (toℕ (x .proj₁)) (- ₁₊ c2) ≡ b₃ →
    ((ract'' ᵗ) (inj₂ ((₀ , b1) , inj₂ ((₁₊ c2 , g2) , lm2))) ((ZM x) ↓ • CZ)) ≋
    ((ract'' ᵗ) (inj₂ ((₀ , b1) , inj₂ ((₁₊ c2 , g2) , lm2)))
      (CZ^ (x ^1) • (ZM x) ↓))
  semiMCZ-go-0c x xs' c2 b1 g2 b₂ b₃ lm2 eq-x eq₂ eq₃ = resid≈ , coset≡
    where
    xv = x .proj₁
    ixv = (x ⁻¹) .proj₁
    inst-x = nztoℕ {y = xv} {neq0 = x .proj₂}
    lm : C (₂₊ m)
    lm = inj₂ ((₁₊ c2 , g2) , lm2)

    c₂fix : ((ract'' ᵗ) (inj₂ ((₀ , b1) , lm)) (ZM x)) .proj₂ ≡
            inj₂ ((₀ , b₂) , lm)
    c₂fix = Eq.trans (MD-coset!0 x b1 lm)
              (Eq.cong (λ v → inj₂ ((₀ , v) , lm)) eq₂)

    nz0 : nsum (toℕ xv) (- ₀) ≡ ₀
    nz0 = Eq.trans (nsum-neg xv ₀)
          (Eq.trans (Eq.cong -_ (*-zeroʳ xv)) -0#≈0#)

    cSfix : ((ract'' ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ ^ toℕ xv)) .proj₂ ≡
            inj₂ ((₀ , b₃) , lm)
    cSfix = Eq.trans (ract-CZ^-coset (₀ , b1) (₁₊ c2 , g2) lm2 (toℕ xv))
      (Eq.cong₂ (λ v w → inj₂ ((₀ , v) , inj₂ ((₁₊ c2 , w) , lm2)))
        eq₃
        (Eq.trans (Eq.cong (g2 +_) nz0) (+-identityʳ g2)))

    W : Word (Gen (₂₊ m))
    W = H ↑ • CZ • (H ↑) ^ 3

    slide : ZM x • W ≈ (H ↑ • (CZ^ (x ^1) • (H ↑) ^ 3)) • ZM x
    slide =
      trans (sym assoc)
      (trans (cong (comm-ZM-↑ x H) refl)
      (trans assoc
      (trans (cong refl (sym assoc))
      (trans (cong refl (cong (MCZ-slide x) refl))
      (trans (cong refl assoc)
      (trans (cong refl (cong refl (comm-ZM-↑ x (H ^ 3))))
      (trans (cong refl (sym assoc))
             (sym assoc))))))))

    pow-fix : ∀ (V : Word (Gen (₂₊ m))) →
      V ^ toℕ xv ≡ V ^ (₁₊ (toℕ xs'))
    pow-fix V = Eq.cong (λ t → V ^ toℕ t) eq-x

    Wpow : W ^ toℕ xv ≈ H ↑ • (CZ^ (x ^1) • (H ↑) ^ 3)
    Wpow =
      trans (refl'ᵣ (pow-fix W))
      (trans (conj-pow (H ↑) CZ ((H ↑) ^ 3) (toℕ xs') H↑3H↑≈ε)
        (refl'ᵣ (Eq.cong (λ t → H ↑ • ((CZ ^ toℕ t) • (H ↑) ^ 3))
          (Eq.sym eq-x))))

    resid≈ : ((ract'' ᵗ) (inj₂ ((₀ , b1) , lm)) ((ZM x) ↓ • CZ)) .proj₁ ≈
             ((ract'' ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ^ (x ^1) • (ZM x) ↓)) .proj₁
    resid≈ =
      trans (refl'ᵣ (Eq.cong (λ w → ((ract'' ᵗ) (inj₂ ((₀ , b1) , lm)) (w • CZ)) .proj₁)
              (M↓≡ x)))
      (trans (cong (MD-resid!0 x b1 lm)
        (refl'ᵣ (Eq.cong (λ c → ((ract'' ᵗ) c CZ) .proj₁) c₂fix)))
      (trans slide
      (sym (trans (refl'ᵣ (Eq.cong (λ w → ((ract'' ᵗ) (inj₂ ((₀ , b1) , lm))
                     (CZ^ (x ^1) • w)) .proj₁) (M↓≡ x)))
           (trans (cong (ract-CZ^-resid (₀ , b1) (₁₊ c2 , g2) lm2 (toℕ xv))
             (refl'ᵣ (Eq.cong (λ c → ((ract'' ᵗ) c (ZM x)) .proj₁) cSfix)))
           (cong Wpow (MD-resid!0 x b₃ lm)))))))

    bfix : b₂ + - ₁₊ c2 ≡ ixv * b₃
    bfix = Eq.sym (Eq.trans (Eq.cong (ixv *_) (Eq.sym eq₃))
      (Eq.trans (Eq.cong (ixv *_)
          (Eq.cong (b1 +_) (nsum-neg xv (₁₊ c2))))
      (Eq.trans (*-distribˡ-+ ixv b1 (- (xv * ₁₊ c2)))
        (Eq.cong₂ _+_ eq₂
          (Eq.trans (Eq.sym (-‿distribʳ-* ixv (xv * ₁₊ c2)))
            (Eq.cong -_
              (Eq.trans (Eq.sym (*-assoc ixv xv (₁₊ c2)))
              (Eq.trans (Eq.cong (_* ₁₊ c2) (lemma-⁻¹ˡ xv {{inst-x}}))
                        (*-identityˡ (₁₊ c2))))))))))

    coset≡ : ((ract'' ᵗ) (inj₂ ((₀ , b1) , lm)) ((ZM x) ↓ • CZ)) .proj₂ ≡
             ((ract'' ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ^ (x ^1) • (ZM x) ↓)) .proj₂
    coset≡ = Eq.trans
      (Eq.cong (λ w → ((ract'' ᵗ) (inj₂ ((₀ , b1) , lm)) (w • CZ)) .proj₂)
        (M↓≡ x))
      (Eq.trans (Eq.cong (λ c → ((ract'' ᵗ) c CZ) .proj₂) c₂fix)
      (Eq.trans
        (Eq.cong₂ (λ v w → inj₂ ((₀ , v) , inj₂ ((₁₊ c2 , w) , lm2)))
          bfix
          (Eq.trans (Eq.cong (g2 +_) -0#≈0#) (+-identityʳ g2)))
      (Eq.sym (Eq.trans
        (Eq.cong (λ w → ((ract'' ᵗ) (inj₂ ((₀ , b1) , lm))
            (CZ^ (x ^1) • w)) .proj₂) (M↓≡ x))
        (Eq.trans (Eq.cong (λ c → ((ract'' ᵗ) c (ZM x)) .proj₂) cSfix)
          (MD-coset!0 x b₃ lm))))))

------------------------------------------------------------------------
-- Pattern (₁₊ a1,·)/(₀,·): the escape is the H-conjugated CZ on the
-- bottom wire; M slides through, inverting at each H.

  private
    module L0 = Lemmas0 (₁₊ m)

  swap-M-H : ∀ (y : ℤ* ₚ) → ZM y • H ≈ H • ZM (y ⁻¹)
  swap-M-H y = sym (trans (L0.semi-HM (y ⁻¹))
    (cong (ZM-val≈ ((y ⁻¹) ⁻¹) y (inv-involutive y)) refl))

  M-H3 : ∀ (y : ℤ* ₚ) → ZM y • H ^ 3 ≈ H ^ 3 • ZM (y ⁻¹)
  M-H3 y =
    trans (sym assoc)
    (trans (cong (swap-M-H y) refl)
    (trans assoc
    (trans (cong refl (sym (L0.aux-comm-HHM (y ⁻¹))))
           (sym assoc))))

  semiMCZ-go-a0 : ∀ (x : ℤ* ₚ) (xs' a1 v1' : Fin (₁₊ p-2))
    (b1 g2 b₂ g₃ : ℤ ₚ) (lm2 : C (₁₊ m)) →
    x .proj₁ ≡ ₁₊ xs' →
    x .proj₁ * ₁₊ a1 ≡ ₁₊ v1' →
    (x ⁻¹) .proj₁ * b1 ≡ b₂ →
    g2 + nsum (toℕ (x .proj₁)) (- ₁₊ a1) ≡ g₃ →
    ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , inj₂ ((₀ , g2) , lm2))) ((ZM x) ↓ • CZ)) ≋
    ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , inj₂ ((₀ , g2) , lm2)))
      (CZ^ (x ^1) • (ZM x) ↓))
  semiMCZ-go-a0 x xs' a1 v1' b1 g2 b₂ g₃ lm2 eq-x eq-v eq₂ eq-g =
    resid≈ , coset≡
    where
    xv = x .proj₁
    lm : C (₂₊ m)
    lm = inj₂ ((₀ , g2) , lm2)
    lm' : C (₂₊ m)
    lm' = inj₂ ((₀ , g₃) , lm2)

    c₂fix : ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , lm)) (ZM x)) .proj₂ ≡
            inj₂ ((₁₊ v1' , b₂) , lm)
    c₂fix = Eq.trans (MD-coset!+ x a1 b1 lm)
              (Eq.cong₂ (λ u v → inj₂ ((u , v) , lm)) eq-v eq₂)

    cSfix : ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , lm)) (CZ ^ toℕ xv)) .proj₂ ≡
            inj₂ ((₁₊ a1 , b1) , lm')
    cSfix = Eq.trans (ract-CZ^-coset (₁₊ a1 , b1) (₀ , g2) lm2 (toℕ xv))
      (Eq.cong₂ (λ v w → inj₂ ((₁₊ a1 , v) , inj₂ ((₀ , w) , lm2)))
        (Eq.trans (Eq.cong (b1 +_)
            (Eq.trans (nsum-neg xv ₀)
              (Eq.trans (Eq.cong -_ (*-zeroʳ xv)) -0#≈0#)))
          (+-identityʳ b1))
        eq-g)

    slide : ZM (x ⁻¹) • (H • (CZ • H ^ 3)) ≈
            (H • (CZ^ (x ^1) • H ^ 3)) • ZM (x ⁻¹)
    slide =
      trans (sym assoc)
      (trans (cong (trans (swap-M-H (x ⁻¹))
                     (cong refl (ZM-val≈ ((x ⁻¹) ⁻¹) x (inv-involutive x))))
                   refl)
      (trans assoc
      (trans (cong refl (sym assoc))
      (trans (cong refl (cong (MCZ-slide x) refl))
      (trans (cong refl assoc)
      (trans (cong refl (cong refl (M-H3 x)))
      (trans (cong refl (sym assoc))
             (sym assoc))))))))

    Wpow : (H • (CZ • H ^ 3)) ^ toℕ xv ≈ H • (CZ^ (x ^1) • H ^ 3)
    Wpow =
      trans (refl'ᵣ (Eq.cong (λ t → (H • (CZ • H ^ 3)) ^ toℕ t) eq-x))
      (trans (conj-pow H CZ (H ^ 3) (toℕ xs') (H3H≈ε {₁₊ m}))
        (refl'ᵣ (Eq.cong (λ t → H • ((CZ ^ toℕ t) • H ^ 3))
          (Eq.sym eq-x))))

    resid≈ : ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , lm)) ((ZM x) ↓ • CZ)) .proj₁ ≈
             ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , lm)) (CZ^ (x ^1) • (ZM x) ↓)) .proj₁
    resid≈ =
      trans (refl'ᵣ (Eq.cong
          (λ w → ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , lm)) (w • CZ)) .proj₁)
          (M↓≡ x)))
      (trans (cong (MD-resid!+ x a1 b1 lm)
        (refl'ᵣ (Eq.cong (λ c → ((ract'' ᵗ) c CZ) .proj₁) c₂fix)))
      (trans slide
      (sym (trans (refl'ᵣ (Eq.cong (λ w → ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , lm))
                     (CZ^ (x ^1) • w)) .proj₁) (M↓≡ x)))
           (trans (cong (ract-CZ^-resid (₁₊ a1 , b1) (₀ , g2) lm2 (toℕ xv))
             (refl'ᵣ (Eq.cong (λ c → ((ract'' ᵗ) c (ZM x)) .proj₁) cSfix)))
           (cong Wpow (MD-resid!+ x a1 b1 lm')))))))

    gfix : g2 + - ₁₊ v1' ≡ g₃
    gfix = Eq.trans
      (Eq.cong (λ t → g2 + - t) (Eq.sym eq-v))
      (Eq.trans (Eq.cong (g2 +_) (Eq.sym (nsum-neg xv (₁₊ a1)))) eq-g)

    coset≡ : ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , lm)) ((ZM x) ↓ • CZ)) .proj₂ ≡
             ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , lm)) (CZ^ (x ^1) • (ZM x) ↓)) .proj₂
    coset≡ = Eq.trans
      (Eq.cong (λ w → ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , lm)) (w • CZ)) .proj₂)
        (M↓≡ x))
      (Eq.trans (Eq.cong (λ c → ((ract'' ᵗ) c CZ) .proj₂) c₂fix)
      (Eq.trans
        (Eq.cong₂ (λ v w → inj₂ ((₁₊ v1' , v) , inj₂ ((₀ , w) , lm2)))
          (Eq.trans (Eq.cong (b₂ +_) -0#≈0#) (+-identityʳ b₂))
          gfix)
      (Eq.sym (Eq.trans
        (Eq.cong (λ w → ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , lm))
            (CZ^ (x ^1) • w)) .proj₂) (M↓≡ x))
        (Eq.trans (Eq.cong (λ c → ((ract'' ᵗ) c (ZM x)) .proj₂) cSfix)
          (Eq.trans (MD-coset!+ x a1 b1 lm')
            (Eq.cong₂ (λ u v → inj₂ ((u , v) , lm')) eq-v eq₂)))))))


------------------------------------------------------------------------
-- S-power of an S-power collapses to the product value (width-generic).
-- Written as an explicit chain: the trans-composed version makes the
-- unifier grind on the mod-arithmetic middles.

module _ {j : ℕ} where
  open PB ((₁₊ j) QRel,_===_)
  open PP ((₁₊ j) QRel,_===_)
  open SR word-setoid
  private module L0j = Lemmas0 j

  Spow-pow : ∀ (y u : ℤ ₚ) → (S^ u) ^ toℕ y ≈ S^ (y * u)
  Spow-pow y u = begin
    (S ^ toℕ u) ^ toℕ y            ≈⟨ ^^ S (toℕ u) (toℕ y) ⟩
    S ^ (toℕ u Nat.* toℕ y)        ≈⟨ refl' (Eq.cong (S ^_) (NP.*-comm (toℕ u) (toℕ y))) ⟩
    S ^ (toℕ y Nat.* toℕ u)        ≈⟨ L0j.lemma-S^k-% (toℕ y Nat.* toℕ u) ⟩
    S ^ ((toℕ y Nat.* toℕ u) % p)  ≈⟨ refl' (Eq.cong (S ^_) (lemma-toℕ-% y u)) ⟩
    S ^ toℕ (y * u) ∎

------------------------------------------------------------------------
-- Pattern (₁₊ a1,·)/(₁₊ c2,·): the fully conjugated escape.

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)
  open PP ((₂₊ m) QRel,_===_)
  open SR word-setoid
  private
    ract'' = ract {₂₊ m}
    module L0m = Lemmas0 (₁₊ m)

  Spow-pow-↑ : ∀ (y v : ℤ ₚ) → (S^ v ↑) ^ toℕ y ≈ S^ (y * v) ↑
  Spow-pow-↑ y v =
    trans (refl' (pow-↑ (S ^ toℕ v) (toℕ y)))
      (lemma-cong↑ ((S ^ toℕ v) ^ toℕ y) (S ^ toℕ (y * v)) (Spow-pow {m} y v))

  QPcc : (H ^ 3 • (H ↑) ^ 3) • (H • H ↑) ≈ ε
  QPcc = begin
    (H ^ 3 • (H ↑) ^ 3) • (H • H ↑)   ≈⟨ assoc ⟩
    H ^ 3 • ((H ↑) ^ 3 • (H • H ↑))   ≈⟨ cright (sym assoc) ⟩
    H ^ 3 • (((H ↑) ^ 3 • H) • H ↑)   ≈⟨ cright (cleft (sym (lemma-comm-H-w↑ (H ^ 3)))) ⟩
    H ^ 3 • ((H • (H ↑) ^ 3) • H ↑)   ≈⟨ cright assoc ⟩
    H ^ 3 • (H • ((H ↑) ^ 3 • H ↑))   ≈⟨ cright (cright (H↑3H↑≈ε {m})) ⟩
    H ^ 3 • (H • ε)                   ≈⟨ cright right-unit ⟩
    H ^ 3 • H                         ≈⟨ H3H≈ε {₁₊ m} ⟩
    ε ∎

  reshape : ∀ (C₀ : Word (Gen (₂₊ m))) (su sv : ℤ ₚ) →
    H • (H ↑ • (C₀ • (S^ su • (H ^ 3 • (S^ sv ↑ • (H ↑) ^ 3))))) ≈
    (H • H ↑) • ((C₀ • (S^ su • S^ sv ↑)) • (H ^ 3 • (H ↑) ^ 3))
  reshape C₀ su sv = begin
    H • (H ↑ • (C₀ • (S^ su • (H ^ 3 • (S^ sv ↑ • (H ↑) ^ 3)))))
      ≈⟨ cright (cright (cright (cright (sym assoc)))) ⟩
    H • (H ↑ • (C₀ • (S^ su • ((H ^ 3 • S^ sv ↑) • (H ↑) ^ 3))))
      ≈⟨ cright (cright (cright (cright (cleft
           (comm⇒pow-comm {w = H} {v = S^ sv ↑} 3 1 (lemma-comm-H-w↑ (S^ sv))))))) ⟩
    H • (H ↑ • (C₀ • (S^ su • ((S^ sv ↑ • H ^ 3) • (H ↑) ^ 3))))
      ≈⟨ cright (cright (cright (cright assoc))) ⟩
    H • (H ↑ • (C₀ • (S^ su • (S^ sv ↑ • (H ^ 3 • (H ↑) ^ 3)))))
      ≈⟨ cright (cright (cright (sym assoc))) ⟩
    H • (H ↑ • (C₀ • ((S^ su • S^ sv ↑) • (H ^ 3 • (H ↑) ^ 3))))
      ≈⟨ cright (cright (sym assoc)) ⟩
    H • (H ↑ • ((C₀ • (S^ su • S^ sv ↑)) • (H ^ 3 • (H ↑) ^ 3)))
      ≈⟨ cright (sym assoc) ⟩
    H • ((H ↑ • (C₀ • (S^ su • S^ sv ↑))) • (H ^ 3 • (H ↑) ^ 3))
      ≈⟨ cright (cleft (sym assoc)) ⟩
    H • (((H ↑ • C₀) • (S^ su • S^ sv ↑)) • (H ^ 3 • (H ↑) ^ 3))
      ≈⟨ cright assoc ⟩
    H • ((H ↑ • C₀) • ((S^ su • S^ sv ↑) • (H ^ 3 • (H ↑) ^ 3)))
      ≈⟨ sym assoc ⟩
    (H • (H ↑ • C₀)) • ((S^ su • S^ sv ↑) • (H ^ 3 • (H ↑) ^ 3))
      ≈⟨ cleft (sym assoc) ⟩
    ((H • H ↑) • C₀) • ((S^ su • S^ sv ↑) • (H ^ 3 • (H ↑) ^ 3))
      ≈⟨ assoc ⟩
    (H • H ↑) • (C₀ • ((S^ su • S^ sv ↑) • (H ^ 3 • (H ↑) ^ 3)))
      ≈⟨ cright (sym assoc) ⟩
    (H • H ↑) • ((C₀ • (S^ su • S^ sv ↑)) • (H ^ 3 • (H ↑) ^ 3)) ∎

  Cx-pow : ∀ (y u v : ℤ ₚ) →
    (CZ • (S^ u • S^ v ↑)) ^ toℕ y ≈
    (CZ ^ toℕ y) • (S^ (y * u) • S^ (y * v) ↑)
  Cx-pow y u v = begin
    (CZ • (S^ u • S^ v ↑)) ^ toℕ y
      ≈⟨ pow-•-comm CZ (S^ u • S^ v ↑) (toℕ y) commT ⟩
    (CZ ^ toℕ y) • ((S^ u • S^ v ↑) ^ toℕ y)
      ≈⟨ cright (pow-•-comm (S^ u) (S^ v ↑) (toℕ y)
           (comm-Spow-↑ (toℕ u) (S^ v))) ⟩
    (CZ ^ toℕ y) • ((S^ u) ^ toℕ y • (S^ v ↑) ^ toℕ y)
      ≈⟨ cright (cong (Spow-pow {₁₊ m} y u) (Spow-pow-↑ y v)) ⟩
    (CZ ^ toℕ y) • (S^ (y * u) • S^ (y * v) ↑) ∎
    where
    commT : CZ • (S^ u • S^ v ↑) ≈ (S^ u • S^ v ↑) • CZ
    commT = begin
      CZ • (S^ u • S^ v ↑)   ≈⟨ sym assoc ⟩
      (CZ • S^ u) • S^ v ↑
        ≈⟨ cleft (comm⇒pow-comm {w = CZ} {v = S} 1 (toℕ u) (axiom comm-CZ-S↓)) ⟩
      (S^ u • CZ) • S^ v ↑   ≈⟨ assoc ⟩
      S^ u • (CZ • S^ v ↑)
        ≈⟨ cright (trans (cright (refl' (Eq.sym (pow-↑ S (toℕ v)))))
             (trans (comm⇒pow-comm {w = CZ} {v = S ↑} 1 (toℕ v) (axiom comm-CZ-S↑))
               (cleft (refl' (pow-↑ S (toℕ v)))))) ⟩
      S^ u • (S^ v ↑ • CZ)   ≈⟨ sym assoc ⟩
      (S^ u • S^ v ↑) • CZ ∎

  semiMCZ-go-cc : ∀ (x : ℤ* ₚ) (xs' a1 v1' c2 : Fin (₁₊ p-2))
    (b1 g2 b₂ b₃ g₃ : ℤ ₚ) (lm2 : C (₁₊ m)) →
    x .proj₁ ≡ ₁₊ xs' →
    x .proj₁ * ₁₊ a1 ≡ ₁₊ v1' →
    (x ⁻¹) .proj₁ * b1 ≡ b₂ →
    b1 + nsum (toℕ (x .proj₁)) (- ₁₊ c2) ≡ b₃ →
    g2 + nsum (toℕ (x .proj₁)) (- ₁₊ a1) ≡ g₃ →
    ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , inj₂ ((₁₊ c2 , g2) , lm2)))
      ((ZM x) ↓ • CZ)) ≋
    ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , inj₂ ((₁₊ c2 , g2) , lm2)))
      (CZ^ (x ^1) • (ZM x) ↓))
  semiMCZ-go-cc x xs' a1 v1' c2 b1 g2 b₂ b₃ g₃ lm2 eq-x eq-v eq₂ eq₃ eq-g =
    resid≈ , coset≡
    where
    xv = x .proj₁
    ixv = (x ⁻¹) .proj₁
    inst-x = nztoℕ {y = xv} {neq0 = x .proj₂}
    lm lm' : C (₂₊ m)
    lm  = inj₂ ((₁₊ c2 , g2) , lm2)
    lm' = inj₂ ((₁₊ c2 , g₃) , lm2)

    iA1 = ((₁₊ a1 , λ ()) ⁻¹) .proj₁
    iC2 = ((₁₊ c2 , λ ()) ⁻¹) .proj₁
    iV1 = ((₁₊ v1' , λ ()) ⁻¹) .proj₁

    u  = - ₁₊ c2 * iA1
    v  = - ₁₊ a1 * iC2
    u' = - ₁₊ c2 * iV1
    v' = - ₁₊ v1' * iC2
    su = u' * (xv * xv)

    padW : ∀ (A C : Fin (₁₊ p-2)) (B G : ℤ ₚ) →
      (DDCZ.dir-of ((₁₊ A , B) ∷ (₁₊ C , G) ∷ []) ↓ᵏ m) ≡
      H • (H ↑ • (CZ • (S^ (- ₁₊ C * ((₁₊ A , λ ()) ⁻¹) .proj₁) •
        (H ^ 3 • (S^ (- ₁₊ A * ((₁₊ C , λ ()) ⁻¹) .proj₁) ↑ • (H ↑) ^ 3)))))
    padW A C B G = Eq.cong₂
      (λ s t → H • (H ↑ • (CZ • (s • (H ^ 3 • (t • (H ↑) ^ 3))))))
      (S^-↓ᵏ (- ₁₊ C * ((₁₊ A , λ ()) ⁻¹) .proj₁) m)
      (Eq.trans (↑↓ᵏ-comm (S^ (- ₁₊ A * ((₁₊ C , λ ()) ⁻¹) .proj₁)) m)
        (Eq.cong _↑ (S^-↓ᵏ (- ₁₊ A * ((₁₊ C , λ ()) ⁻¹) .proj₁) m)))

    c₂fix : ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , lm)) (ZM x)) .proj₂ ≡
            inj₂ ((₁₊ v1' , b₂) , lm)
    c₂fix = Eq.trans (MD-coset!+ x a1 b1 lm)
              (Eq.cong₂ (λ p₁ q₁ → inj₂ ((p₁ , q₁) , lm)) eq-v eq₂)

    cSfix : ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , lm)) (CZ ^ toℕ xv)) .proj₂ ≡
            inj₂ ((₁₊ a1 , b₃) , lm')
    cSfix = Eq.trans (ract-CZ^-coset (₁₊ a1 , b1) (₁₊ c2 , g2) lm2 (toℕ xv))
      (Eq.cong₂ (λ p₁ q₁ → inj₂ ((₁₊ a1 , p₁) , inj₂ ((₁₊ c2 , q₁) , lm2)))
        eq₃ eq-g)

    swapfix : ZM (x ⁻¹) • H ≈ H • ZM x
    swapfix = trans (swap-M-H (x ⁻¹))
      (cong refl (ZM-val≈ ((x ⁻¹) ⁻¹) x (inv-involutive x)))

    slide : ZM (x ⁻¹) •
        (H • (H ↑ • (CZ • (S^ u' • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3)))))) ≈
      (H • (H ↑ • (CZ^ (x ^1) • (S^ su • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3)))))) •
        ZM (x ⁻¹)
    slide = begin
      ZM (x ⁻¹) • (H • (H ↑ • (CZ • (S^ u' • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3))))))
        ≈⟨ sym assoc ⟩
      (ZM (x ⁻¹) • H) • (H ↑ • (CZ • (S^ u' • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3)))))
        ≈⟨ cleft swapfix ⟩
      (H • ZM x) • (H ↑ • (CZ • (S^ u' • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3)))))
        ≈⟨ assoc ⟩
      H • (ZM x • (H ↑ • (CZ • (S^ u' • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3))))))
        ≈⟨ cright (sym assoc) ⟩
      H • ((ZM x • H ↑) • (CZ • (S^ u' • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3)))))
        ≈⟨ cright (cleft (comm-ZM-↑ x H)) ⟩
      H • ((H ↑ • ZM x) • (CZ • (S^ u' • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3)))))
        ≈⟨ cright assoc ⟩
      H • (H ↑ • (ZM x • (CZ • (S^ u' • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3))))))
        ≈⟨ cright (cright (sym assoc)) ⟩
      H • (H ↑ • ((ZM x • CZ) • (S^ u' • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3)))))
        ≈⟨ cright (cright (cleft (MCZ-slide x))) ⟩
      H • (H ↑ • ((CZ^ (x ^1) • ZM x) • (S^ u' • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3)))))
        ≈⟨ cright (cright assoc) ⟩
      H • (H ↑ • (CZ^ (x ^1) • (ZM x • (S^ u' • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3))))))
        ≈⟨ cright (cright (cright (sym assoc))) ⟩
      H • (H ↑ • (CZ^ (x ^1) • ((ZM x • S^ u') • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3)))))
        ≈⟨ cright (cright (cright (cleft (L0m.lemma-MS^k xv u' (x .proj₂))))) ⟩
      H • (H ↑ • (CZ^ (x ^1) • ((S^ su • ZM x) • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3)))))
        ≈⟨ cright (cright (cright assoc)) ⟩
      H • (H ↑ • (CZ^ (x ^1) • (S^ su • (ZM x • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3))))))
        ≈⟨ cright (cright (cright (cright (sym assoc)))) ⟩
      H • (H ↑ • (CZ^ (x ^1) • (S^ su • ((ZM x • H ^ 3) • (S^ v' ↑ • (H ↑) ^ 3)))))
        ≈⟨ cright (cright (cright (cright (cleft (M-H3 x))))) ⟩
      H • (H ↑ • (CZ^ (x ^1) • (S^ su • ((H ^ 3 • ZM (x ⁻¹)) • (S^ v' ↑ • (H ↑) ^ 3)))))
        ≈⟨ cright (cright (cright (cright assoc))) ⟩
      H • (H ↑ • (CZ^ (x ^1) • (S^ su • (H ^ 3 • (ZM (x ⁻¹) • (S^ v' ↑ • (H ↑) ^ 3))))))
        ≈⟨ cright (cright (cright (cright (cright (sym assoc))))) ⟩
      H • (H ↑ • (CZ^ (x ^1) • (S^ su • (H ^ 3 • ((ZM (x ⁻¹) • S^ v' ↑) • (H ↑) ^ 3)))))
        ≈⟨ cright (cright (cright (cright (cright (cleft (comm-ZM-↑ (x ⁻¹) (S^ v'))))))) ⟩
      H • (H ↑ • (CZ^ (x ^1) • (S^ su • (H ^ 3 • ((S^ v' ↑ • ZM (x ⁻¹)) • (H ↑) ^ 3)))))
        ≈⟨ cright (cright (cright (cright (cright assoc)))) ⟩
      H • (H ↑ • (CZ^ (x ^1) • (S^ su • (H ^ 3 • (S^ v' ↑ • (ZM (x ⁻¹) • (H ↑) ^ 3))))))
        ≈⟨ cright (cright (cright (cright (cright (cright (comm-ZM-↑ (x ⁻¹) (H ^ 3))))))) ⟩
      H • (H ↑ • (CZ^ (x ^1) • (S^ su • (H ^ 3 • (S^ v' ↑ • ((H ↑) ^ 3 • ZM (x ⁻¹)))))))
        ≈⟨ cright (cright (cright (cright (cright (sym assoc))))) ⟩
      H • (H ↑ • (CZ^ (x ^1) • (S^ su • (H ^ 3 • ((S^ v' ↑ • (H ↑) ^ 3) • ZM (x ⁻¹))))))
        ≈⟨ cright (cright (cright (cright (sym assoc)))) ⟩
      H • (H ↑ • (CZ^ (x ^1) • (S^ su • ((H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3)) • ZM (x ⁻¹)))))
        ≈⟨ cright (cright (cright (sym assoc))) ⟩
      H • (H ↑ • (CZ^ (x ^1) • ((S^ su • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3))) • ZM (x ⁻¹))))
        ≈⟨ cright (cright (sym assoc)) ⟩
      H • (H ↑ • ((CZ^ (x ^1) • (S^ su • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3)))) • ZM (x ⁻¹)))
        ≈⟨ cright (sym assoc) ⟩
      H • ((H ↑ • (CZ^ (x ^1) • (S^ su • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3))))) • ZM (x ⁻¹))
        ≈⟨ sym assoc ⟩
      (H • (H ↑ • (CZ^ (x ^1) • (S^ su • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3)))))) • ZM (x ⁻¹) ∎

    iV1≡ : iV1 ≡ ixv * iA1
    iV1≡ = Eq.trans
      (inv-cong (₁₊ v1' , λ ()) (x *' (₁₊ a1 , λ ())) (Eq.sym eq-v))
      (inv-distrib x (₁₊ a1 , λ ()))

    uu : su ≡ xv * u
    uu = Eq.trans (Eq.cong (λ t → (- ₁₊ c2 * t) * (xv * xv)) iV1≡)
      (Eq.trans (Eq.cong (_* (xv * xv)) (Eq.sym (*-assoc (- ₁₊ c2) ixv iA1)))
      (Eq.trans (*-assoc (- ₁₊ c2 * ixv) iA1 (xv * xv))
      (Eq.trans (Eq.cong ((- ₁₊ c2 * ixv) *_) (Eq.sym (*-assoc iA1 xv xv)))
      (Eq.trans (Eq.sym (*-assoc (- ₁₊ c2 * ixv) (iA1 * xv) xv))
      (Eq.trans (Eq.cong (_* xv)
          (Eq.trans (*-assoc (- ₁₊ c2) ixv (iA1 * xv))
            (Eq.cong ((- ₁₊ c2) *_)
              (Eq.trans (Eq.cong (ixv *_) (*-comm iA1 xv))
              (Eq.trans (Eq.sym (*-assoc ixv xv iA1))
              (Eq.trans (Eq.cong (_* iA1) (lemma-⁻¹ˡ xv {{inst-x}}))
                        (*-identityˡ iA1)))))))
        (*-comm (- ₁₊ c2 * iA1) xv))))))

    vv : v' ≡ xv * v
    vv = Eq.trans (Eq.cong (λ t → - t * iC2) (Eq.sym eq-v))
      (Eq.trans (Eq.cong (_* iC2) (-‿distribʳ-* xv (₁₊ a1)))
        (*-assoc xv (- ₁₊ a1) iC2))

    Wpow : (DDCZ.dir-of ((₁₊ a1 , b1) ∷ (₁₊ c2 , g2) ∷ []) ↓ᵏ m) ^ toℕ xv ≈
           (H • H ↑) • ((CZ^ (x ^1) • (S^ (xv * u) • S^ (xv * v) ↑)) •
             (H ^ 3 • (H ↑) ^ 3))
    Wpow = begin
      (DDCZ.dir-of ((₁₊ a1 , b1) ∷ (₁₊ c2 , g2) ∷ []) ↓ᵏ m) ^ toℕ xv
        ≈⟨ refl' (Eq.cong (_^ toℕ xv) (padW a1 c2 b1 g2)) ⟩
      (H • (H ↑ • (CZ • (S^ u • (H ^ 3 • (S^ v ↑ • (H ↑) ^ 3)))))) ^ toℕ xv
        ≈⟨ ^-cong _ _ (toℕ xv) (reshape CZ u v) ⟩
      ((H • H ↑) • ((CZ • (S^ u • S^ v ↑)) • (H ^ 3 • (H ↑) ^ 3))) ^ toℕ xv
        ≈⟨ refl' (Eq.cong
             (λ t → ((H • H ↑) • ((CZ • (S^ u • S^ v ↑)) • (H ^ 3 • (H ↑) ^ 3))) ^ toℕ t)
             eq-x) ⟩
      ((H • H ↑) • ((CZ • (S^ u • S^ v ↑)) • (H ^ 3 • (H ↑) ^ 3))) ^ (₁₊ (toℕ xs'))
        ≈⟨ conj-pow (H • H ↑) (CZ • (S^ u • S^ v ↑)) (H ^ 3 • (H ↑) ^ 3)
             (toℕ xs') QPcc ⟩
      (H • H ↑) • ((CZ • (S^ u • S^ v ↑)) ^ (₁₊ (toℕ xs')) • (H ^ 3 • (H ↑) ^ 3))
        ≈⟨ cright (cleft (refl' (Eq.cong (λ t → (CZ • (S^ u • S^ v ↑)) ^ toℕ t)
             (Eq.sym eq-x)))) ⟩
      (H • H ↑) • ((CZ • (S^ u • S^ v ↑)) ^ toℕ xv • (H ^ 3 • (H ↑) ^ 3))
        ≈⟨ cright (cleft (Cx-pow xv u v)) ⟩
      (H • H ↑) • (((CZ ^ toℕ xv) • (S^ (xv * u) • S^ (xv * v) ↑)) • (H ^ 3 • (H ↑) ^ 3)) ∎

    resid≈ : ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , lm)) ((ZM x) ↓ • CZ)) .proj₁ ≈
             ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , lm)) (CZ^ (x ^1) • (ZM x) ↓)) .proj₁
    resid≈ =
      trans (refl' (Eq.cong
          (λ w → ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , lm)) (w • CZ)) .proj₁)
          (M↓≡ x)))
      (trans (cong (MD-resid!+ x a1 b1 lm)
        (refl' (Eq.trans
          (Eq.cong (λ c → ((ract'' ᵗ) c CZ) .proj₁) c₂fix)
          (padW v1' c2 b₂ g2))))
      (trans slide
      (trans (cong (refl' (Eq.cong
          (λ t → H • (H ↑ • (CZ^ (x ^1) • (S^ t • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3))))))
          uu)) refl)
      (trans (cong (refl' (Eq.cong
          (λ t → H • (H ↑ • (CZ^ (x ^1) • (S^ (xv * u) • (H ^ 3 • (S^ t ↑ • (H ↑) ^ 3))))))
          vv)) refl)
      (trans (cong (reshape (CZ^ (x ^1)) (xv * u) (xv * v)) refl)
      (sym (trans (refl' (Eq.cong (λ w → ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , lm))
                     (CZ^ (x ^1) • w)) .proj₁) (M↓≡ x)))
           (trans (cong (ract-CZ^-resid (₁₊ a1 , b1) (₁₊ c2 , g2) lm2 (toℕ xv))
             (refl' (Eq.cong (λ c → ((ract'' ᵗ) c (ZM x)) .proj₁) cSfix)))
           (cong Wpow (MD-resid!+ x a1 b₃ lm'))))))))))

    bfix : b₂ + - ₁₊ c2 ≡ ixv * b₃
    bfix = Eq.sym (Eq.trans (Eq.cong (ixv *_) (Eq.sym eq₃))
      (Eq.trans (Eq.cong (ixv *_)
          (Eq.cong (b1 +_) (nsum-neg xv (₁₊ c2))))
      (Eq.trans (*-distribˡ-+ ixv b1 (- (xv * ₁₊ c2)))
        (Eq.cong₂ _+_ eq₂
          (Eq.trans (Eq.sym (-‿distribʳ-* ixv (xv * ₁₊ c2)))
            (Eq.cong -_
              (Eq.trans (Eq.sym (*-assoc ixv xv (₁₊ c2)))
              (Eq.trans (Eq.cong (_* ₁₊ c2) (lemma-⁻¹ˡ xv {{inst-x}}))
                        (*-identityˡ (₁₊ c2))))))))))

    gfix : g2 + - ₁₊ v1' ≡ g₃
    gfix = Eq.trans
      (Eq.cong (λ t → g2 + - t) (Eq.sym eq-v))
      (Eq.trans (Eq.cong (g2 +_) (Eq.sym (nsum-neg xv (₁₊ a1)))) eq-g)

    coset≡ : ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , lm)) ((ZM x) ↓ • CZ)) .proj₂ ≡
             ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , lm)) (CZ^ (x ^1) • (ZM x) ↓)) .proj₂
    coset≡ = Eq.trans
      (Eq.cong (λ w → ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , lm)) (w • CZ)) .proj₂)
        (M↓≡ x))
      (Eq.trans (Eq.cong (λ c → ((ract'' ᵗ) c CZ) .proj₂) c₂fix)
      (Eq.trans
        (Eq.cong₂ (λ p₁ q₁ → inj₂ ((₁₊ v1' , p₁) , inj₂ ((₁₊ c2 , q₁) , lm2)))
          bfix gfix)
      (Eq.sym (Eq.trans
        (Eq.cong (λ w → ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , lm))
            (CZ^ (x ^1) • w)) .proj₂) (M↓≡ x))
        (Eq.trans (Eq.cong (λ c → ((ract'' ᵗ) c (ZM x)) .proj₂) cSfix)
          (Eq.trans (MD-coset!+ x a1 b₃ lm')
            (Eq.cong₂ (λ p₁ q₁ → inj₂ ((p₁ , q₁) , lm')) eq-v Eq.refl)))))))
