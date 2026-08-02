------------------------------------------------------------------------
-- Presentations of groups
--
-- The lifted-word traversal engine: threading w ↑ over an inj₂ coset
-- is threading w over the tail coset with the escapes lifted.  Basis
-- for the semi-M↑CZ inj₂-inj₂ cases.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ2
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (inj₁ ; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

open import Word.Base

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase p-2 p-prime

------------------------------------------------------------------------
-- Threading a lifted word: the top D box is untouched and the escapes
-- are the lifted escapes of the tail threading.

ract-↑-≡ : ∀ {n} (d1 : D) (lm : C (₁₊ n)) (w : Circuit (₁₊ n)) →
  ((ract {₁₊ n} ᵗ) (inj₂ (d1 , lm)) (w ↑)) ≡
  ((((ract {n} ᵗ) lm w) .proj₁) ↑ , inj₂ (d1 , ((ract {n} ᵗ) lm w) .proj₂))
ract-↑-≡ d1 lm [ g ]ʷ = Eq.refl
ract-↑-≡ d1 lm ε = Eq.refl
ract-↑-≡ {n} d1 lm (u • v) =
  Eq.trans
    (Eq.cong (λ pr →
        (pr .proj₁ • ((ract {₁₊ n} ᵗ) (pr .proj₂) (v ↑)) .proj₁ ,
         ((ract {₁₊ n} ᵗ) (pr .proj₂) (v ↑)) .proj₂))
      (ract-↑-≡ d1 lm u))
    (Eq.cong (λ pr →
        ((((ract {n} ᵗ) lm u) .proj₁) ↑ • pr .proj₁ , pr .proj₂))
      (ract-↑-≡ d1 (((ract {n} ᵗ) lm u) .proj₂) v))

------------------------------------------------------------------------
-- Width-generic M/H conjugation facts, and their lifted images.

open import Data.Fin using (Fin ; toℕ)
open import Data.Vec using ([] ; _∷_)
open Eq using (_≢_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR
import Data.Nat.Properties as NP
import Data.Nat as Nat
open Lemmas-Sym using (lemma-comm-S-w↑ ; lemma-comm-H-w↑ ; lemma-cong↑)
open import Algebra.Properties.Ring (+-*-ring p-2)
  using (-0#≈0# ; -‿distribʳ-*)
import Examples.Groups.Symplectic.BR.Three.DD-CZ p-2 p-prime as DDCZ
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDM p-2 p-prime
  using (nsum-* ; nsum-neg)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDZM p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDCZ p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMD p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ p-2 p-prime
open import Examples.Groups.Symplectic.CongDownK p-2 p-prime
  using (S^-↓ᵏ ; ↑↓ᵏ-comm)

module _ {j : ℕ} where
  open PB ((₁₊ j) QRel,_===_)
  private module L0j = Lemmas0 j

  swap-M-H-g : ∀ (y : ℤ* ₚ) → ZM y • H ≈ H • ZM (y ⁻¹)
  swap-M-H-g y = sym (trans (L0j.semi-HM (y ⁻¹))
    (cong (ZM-val≈ ((y ⁻¹) ⁻¹) y (inv-involutive y)) refl))

  M-H3-g : ∀ (y : ℤ* ₚ) → ZM y • H ^ 3 ≈ H ^ 3 • ZM (y ⁻¹)
  M-H3-g y =
    trans (sym assoc)
    (trans (cong (swap-M-H-g y) refl)
    (trans assoc
    (trans (cong refl (sym (L0j.aux-comm-HHM (y ⁻¹))))
           (sym assoc))))

------------------------------------------------------------------------
-- Lifted conjugation facts at width ₂₊ m.

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)
  open PP ((₂₊ m) QRel,_===_)
  open SR word-setoid
  private
    ract'' = ract {₂₊ m}
    module L0m1 = Lemmas0 m

  swapfix-↑ : ∀ (x : ℤ* ₚ) → (ZM (x ⁻¹)) ↑ • H ↑ ≈ H ↑ • (ZM x) ↑
  swapfix-↑ x = lemma-cong↑ (ZM (x ⁻¹) • H) (H • ZM x) inner
    where
    module PBm = PB ((₁₊ m) QRel,_===_)
    inner : PBm._≈_ (ZM (x ⁻¹) • H) (H • ZM x)
    inner = PBm.trans (swap-M-H-g {m} (x ⁻¹))
      (PBm.cong PBm.refl (ZM-val≈ ((x ⁻¹) ⁻¹) x (inv-involutive x)))

  M-H3-↑ : ∀ (x : ℤ* ₚ) → (ZM x) ↑ • (H ↑) ^ 3 ≈ (H ↑) ^ 3 • (ZM (x ⁻¹)) ↑
  M-H3-↑ x =
    trans (refl' (Eq.cong ((ZM x) ↑ •_) (pow-↑ H 3)))
    (trans (lemma-cong↑ (ZM x • H ^ 3) (H ^ 3 • ZM (x ⁻¹)) (M-H3-g {m} x))
      (refl' (Eq.cong (_• (ZM (x ⁻¹)) ↑) (Eq.sym (pow-↑ H 3)))))

  MS-slide-↑ : ∀ (x : ℤ* ₚ) (t : ℤ ₚ) →
    (ZM x) ↑ • S^ t ↑ ≈ S^ (t * (x .proj₁ * x .proj₁)) ↑ • (ZM x) ↑
  MS-slide-↑ x t = lemma-cong↑ (ZM x • S^ t)
    (S^ (t * (x .proj₁ * x .proj₁)) • ZM x)
    (L0m1.lemma-MS^k (x .proj₁) t (x .proj₂))

  MCZ-slide-↑ : ∀ (x : ℤ* ₚ) → (ZM x) ↑ • CZ ≈ CZ^ (x ^1) • (ZM x) ↑
  MCZ-slide-↑ x = axiom (semi-M↑CZ x)

  comm-Mup-H : ∀ (y : ℤ* ₚ) → (ZM y) ↑ • H ≈ H • (ZM y) ↑
  comm-Mup-H y = sym (lemma-comm-H-w↑ (ZM y))

  comm-Mup-H3 : ∀ (y : ℤ* ₚ) → (ZM y) ↑ • H ^ 3 ≈ H ^ 3 • (ZM y) ↑
  comm-Mup-H3 y = sym (comm⇒pow-comm {w = H} {v = (ZM y) ↑} 3 1
    (lemma-comm-H-w↑ (ZM y)))

  comm-Mup-Spow : ∀ (y : ℤ* ₚ) (t : ℤ ₚ) →
    (ZM y) ↑ • S^ t ≈ S^ t • (ZM y) ↑
  comm-Mup-Spow y t = sym (comm-Spow-↑ (toℕ t) (ZM y))

------------------------------------------------------------------------
-- semi-M↑CZ on doubly-inj₂ cosets: the lifted M word threads the
-- second D box (ract-↑-≡), and the axiom applies directly since its
-- words are already in ↑-form.

  private
    lift-inner : ∀ (d1 : D) (lm : C (₁₊ (₁₊ m))) (w : Circuit (₁₊ (₁₊ m)))
      (rest : Circuit (₂₊ (₁₊ m))) →
      ((ract'' ᵗ) (inj₂ (d1 , lm)) (w ↑ • rest)) .proj₁ ≡
      ((((ract {₁₊ m} ᵗ) lm w) .proj₁) ↑ •
        ((ract'' ᵗ) (inj₂ (d1 , (((ract {₁₊ m} ᵗ) lm w) .proj₂))) rest) .proj₁)
    lift-inner d1 lm w rest =
      Eq.cong (λ pr → pr .proj₁ • ((ract'' ᵗ) (pr .proj₂) rest) .proj₁)
        (ract-↑-≡ d1 lm w)

    lift-inner₂ : ∀ (d1 : D) (lm : C (₁₊ (₁₊ m))) (w : Circuit (₁₊ (₁₊ m)))
      (rest : Circuit (₂₊ (₁₊ m))) →
      ((ract'' ᵗ) (inj₂ (d1 , lm)) (w ↑ • rest)) .proj₂ ≡
      ((ract'' ᵗ) (inj₂ (d1 , (((ract {₁₊ m} ᵗ) lm w) .proj₂))) rest) .proj₂
    lift-inner₂ d1 lm w rest =
      Eq.cong (λ pr → ((ract'' ᵗ) (pr .proj₂) rest) .proj₂)
        (ract-↑-≡ d1 lm w)

    lift-last : ∀ (d1 : D) (lm : C (₁₊ (₁₊ m))) (w : Circuit (₁₊ (₁₊ m))) →
      ((ract'' ᵗ) (inj₂ (d1 , lm)) (w ↑)) .proj₁ ≡
      (((ract {₁₊ m} ᵗ) lm w) .proj₁) ↑
    lift-last d1 lm w = Eq.cong proj₁ (ract-↑-≡ d1 lm w)

    lift-last₂ : ∀ (d1 : D) (lm : C (₁₊ (₁₊ m))) (w : Circuit (₁₊ (₁₊ m))) →
      ((ract'' ᵗ) (inj₂ (d1 , lm)) (w ↑)) .proj₂ ≡
      inj₂ (d1 , (((ract {₁₊ m} ᵗ) lm w) .proj₂))
    lift-last₂ d1 lm w = Eq.cong proj₂ (ract-↑-≡ d1 lm w)

  semiMuCZ-go-00 : ∀ (x : ℤ* ₚ) (b1 g2 g₂' : ℤ ₚ) (lm2 : C (₁₊ m)) →
    (x ⁻¹) .proj₁ * g2 ≡ g₂' →
    ((ract'' ᵗ) (inj₂ ((₀ , b1) , inj₂ ((₀ , g2) , lm2))) ((ZM x) ↑ • CZ)) ≋
    ((ract'' ᵗ) (inj₂ ((₀ , b1) , inj₂ ((₀ , g2) , lm2)))
      (CZ^ (x ^1) • (ZM x) ↑))
  semiMuCZ-go-00 x b1 g2 g₂' lm2 eq₂ = resid≈ , coset≡
    where
    xv = x .proj₁
    lm lmM : C (₂₊ m)
    lm  = inj₂ ((₀ , g2) , lm2)
    lmM = inj₂ ((₀ , g₂') , lm2)

    ifix : ((ract {₁₊ m} ᵗ) lm (ZM x)) .proj₂ ≡ inj₂ ((₀ , g₂') , lm2)
    ifix = Eq.trans (MD-coset!0 x g2 lm2)
             (Eq.cong (λ v → inj₂ ((₀ , v) , lm2)) eq₂)

    nz0 : nsum (toℕ xv) (- ₀) ≡ ₀
    nz0 = Eq.trans (nsum-neg xv ₀)
          (Eq.trans (Eq.cong -_ (*-zeroʳ xv)) -0#≈0#)

    cSfix : ((ract'' ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ ^ toℕ xv)) .proj₂ ≡
            inj₂ ((₀ , b1) , lm)
    cSfix = Eq.trans (ract-CZ^-coset (₀ , b1) (₀ , g2) lm2 (toℕ xv))
      (Eq.cong₂ (λ v w → inj₂ ((₀ , v) , inj₂ ((₀ , w) , lm2)))
        (Eq.trans (Eq.cong (b1 +_) nz0) (+-identityʳ b1))
        (Eq.trans (Eq.cong (g2 +_) nz0) (+-identityʳ g2)))

    resid≈ : ((ract'' ᵗ) (inj₂ ((₀ , b1) , lm)) ((ZM x) ↑ • CZ)) .proj₁ ≈
             ((ract'' ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ^ (x ^1) • (ZM x) ↑)) .proj₁
    resid≈ =
      trans (refl' (Eq.trans (lift-inner (₀ , b1) lm (ZM x) CZ)
        (Eq.cong (λ c → (_↑ (((ract {₁₊ m} ᵗ) lm (ZM x)) .proj₁)) •
            ((ract'' ᵗ) c CZ) .proj₁)
          (Eq.cong (λ c' → inj₂ ((₀ , b1) , c')) ifix))))
      (trans (cong (lemma-cong↑ (((ract {₁₊ m} ᵗ) lm (ZM x)) .proj₁) (ZM x)
               (MD-resid!0 x g2 lm2)) refl)
      (trans (axiom (semi-M↑CZ x))
      (sym (trans (cong (ract-CZ^-resid (₀ , b1) (₀ , g2) lm2 (toℕ xv))
             (refl' (Eq.trans
               (Eq.cong (λ c → ((ract'' ᵗ) c ((ZM x) ↑)) .proj₁) cSfix)
               (lift-last (₀ , b1) lm (ZM x)))))
           (cong refl (lemma-cong↑ (((ract {₁₊ m} ᵗ) lm (ZM x)) .proj₁) (ZM x)
             (MD-resid!0 x g2 lm2)))))))

    coset≡ : ((ract'' ᵗ) (inj₂ ((₀ , b1) , lm)) ((ZM x) ↑ • CZ)) .proj₂ ≡
             ((ract'' ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ^ (x ^1) • (ZM x) ↑)) .proj₂
    coset≡ = Eq.trans (lift-inner₂ (₀ , b1) lm (ZM x) CZ)
      (Eq.trans (Eq.cong (λ c → ((ract'' ᵗ) (inj₂ ((₀ , b1) , c)) CZ) .proj₂)
          ifix)
      (Eq.trans
        (Eq.cong₂ (λ v w → inj₂ ((₀ , v) , inj₂ ((₀ , w) , lm2)))
          (Eq.trans (Eq.cong (b1 +_) -0#≈0#) (+-identityʳ b1))
          (Eq.trans (Eq.cong (g₂' +_) -0#≈0#) (+-identityʳ g₂')))
      (Eq.sym (Eq.trans
        (Eq.cong (λ c → ((ract'' ᵗ) c ((ZM x) ↑)) .proj₂) cSfix)
        (Eq.trans (lift-last₂ (₀ , b1) lm (ZM x))
          (Eq.cong (λ c → inj₂ ((₀ , b1) , c)) ifix))))))

  semiMuCZ-go-0c : ∀ (x : ℤ* ₚ) (xs' c2 w2' : Fin (₁₊ p-2))
    (b1 g2 g₂' b₃ : ℤ ₚ) (lm2 : C (₁₊ m)) →
    x .proj₁ ≡ ₁₊ xs' →
    x .proj₁ * ₁₊ c2 ≡ ₁₊ w2' →
    (x ⁻¹) .proj₁ * g2 ≡ g₂' →
    b1 + nsum (toℕ (x .proj₁)) (- ₁₊ c2) ≡ b₃ →
    ((ract'' ᵗ) (inj₂ ((₀ , b1) , inj₂ ((₁₊ c2 , g2) , lm2))) ((ZM x) ↑ • CZ)) ≋
    ((ract'' ᵗ) (inj₂ ((₀ , b1) , inj₂ ((₁₊ c2 , g2) , lm2)))
      (CZ^ (x ^1) • (ZM x) ↑))
  semiMuCZ-go-0c x xs' c2 w2' b1 g2 g₂' b₃ lm2 eq-x eq-w eq₂ eq₃ =
    resid≈ , coset≡
    where
    xv = x .proj₁
    ixv = (x ⁻¹) .proj₁
    inst-x = nztoℕ {y = xv} {neq0 = x .proj₂}
    lm lmM : C (₂₊ m)
    lm  = inj₂ ((₁₊ c2 , g2) , lm2)
    lmM = inj₂ ((₁₊ w2' , g₂') , lm2)

    ifix : ((ract {₁₊ m} ᵗ) lm (ZM x)) .proj₂ ≡ lmM
    ifix = Eq.trans (MD-coset!+ x c2 g2 lm2)
             (Eq.cong₂ (λ p₁ q₁ → inj₂ ((p₁ , q₁) , lm2)) eq-w eq₂)

    nz0 : nsum (toℕ xv) (- ₀) ≡ ₀
    nz0 = Eq.trans (nsum-neg xv ₀)
          (Eq.trans (Eq.cong -_ (*-zeroʳ xv)) -0#≈0#)

    cSfix : ((ract'' ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ ^ toℕ xv)) .proj₂ ≡
            inj₂ ((₀ , b₃) , lm)
    cSfix = Eq.trans (ract-CZ^-coset (₀ , b1) (₁₊ c2 , g2) lm2 (toℕ xv))
      (Eq.cong₂ (λ v w → inj₂ ((₀ , v) , inj₂ ((₁₊ c2 , w) , lm2)))
        eq₃
        (Eq.trans (Eq.cong (g2 +_) nz0) (+-identityʳ g2)))

    slide : (ZM (x ⁻¹)) ↑ • (H ↑ • (CZ • (H ↑) ^ 3)) ≈
            (H ↑ • (CZ^ (x ^1) • (H ↑) ^ 3)) • (ZM (x ⁻¹)) ↑
    slide = begin
      (ZM (x ⁻¹)) ↑ • (H ↑ • (CZ • (H ↑) ^ 3))   ≈⟨ sym assoc ⟩
      ((ZM (x ⁻¹)) ↑ • H ↑) • (CZ • (H ↑) ^ 3)   ≈⟨ cleft (swapfix-↑ x) ⟩
      (H ↑ • (ZM x) ↑) • (CZ • (H ↑) ^ 3)        ≈⟨ assoc ⟩
      H ↑ • ((ZM x) ↑ • (CZ • (H ↑) ^ 3))        ≈⟨ cright (sym assoc) ⟩
      H ↑ • (((ZM x) ↑ • CZ) • (H ↑) ^ 3)        ≈⟨ cright (cleft (MCZ-slide-↑ x)) ⟩
      H ↑ • ((CZ^ (x ^1) • (ZM x) ↑) • (H ↑) ^ 3)  ≈⟨ cright assoc ⟩
      H ↑ • (CZ^ (x ^1) • ((ZM x) ↑ • (H ↑) ^ 3))  ≈⟨ cright (cright (M-H3-↑ x)) ⟩
      H ↑ • (CZ^ (x ^1) • ((H ↑) ^ 3 • (ZM (x ⁻¹)) ↑))  ≈⟨ cright (sym assoc) ⟩
      H ↑ • ((CZ^ (x ^1) • (H ↑) ^ 3) • (ZM (x ⁻¹)) ↑)  ≈⟨ sym assoc ⟩
      (H ↑ • (CZ^ (x ^1) • (H ↑) ^ 3)) • (ZM (x ⁻¹)) ↑ ∎

    Wpow : (H ↑ • (CZ • (H ↑) ^ 3)) ^ toℕ xv ≈ H ↑ • (CZ^ (x ^1) • (H ↑) ^ 3)
    Wpow =
      trans (refl' (Eq.cong (λ t → (H ↑ • (CZ • (H ↑) ^ 3)) ^ toℕ t) eq-x))
      (trans (conj-pow (H ↑) CZ ((H ↑) ^ 3) (toℕ xs') (H↑3H↑≈ε {m}))
        (refl' (Eq.cong (λ t → H ↑ • ((CZ ^ toℕ t) • (H ↑) ^ 3))
          (Eq.sym eq-x))))

    resid≈ : ((ract'' ᵗ) (inj₂ ((₀ , b1) , lm)) ((ZM x) ↑ • CZ)) .proj₁ ≈
             ((ract'' ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ^ (x ^1) • (ZM x) ↑)) .proj₁
    resid≈ =
      trans (refl' (Eq.trans (lift-inner (₀ , b1) lm (ZM x) CZ)
        (Eq.cong (λ c → (_↑ (((ract {₁₊ m} ᵗ) lm (ZM x)) .proj₁)) •
            ((ract'' ᵗ) c CZ) .proj₁)
          (Eq.cong (λ c' → inj₂ ((₀ , b1) , c')) ifix))))
      (trans (cong (lemma-cong↑ (((ract {₁₊ m} ᵗ) lm (ZM x)) .proj₁) (ZM (x ⁻¹))
               (MD-resid!+ x c2 g2 lm2)) refl)
      (trans slide
      (sym (trans (cong (ract-CZ^-resid (₀ , b1) (₁₊ c2 , g2) lm2 (toℕ xv))
             (refl' (Eq.trans
               (Eq.cong (λ c → ((ract'' ᵗ) c ((ZM x) ↑)) .proj₁) cSfix)
               (lift-last (₀ , b₃) lm (ZM x)))))
           (cong Wpow (lemma-cong↑ (((ract {₁₊ m} ᵗ) lm (ZM x)) .proj₁)
             (ZM (x ⁻¹)) (MD-resid!+ x c2 g2 lm2)))))))

    bfix : b1 + - ₁₊ w2' ≡ b₃
    bfix = Eq.trans
      (Eq.cong (λ t → b1 + - t) (Eq.sym eq-w))
      (Eq.trans (Eq.cong (b1 +_) (Eq.sym (nsum-neg xv (₁₊ c2)))) eq₃)

    coset≡ : ((ract'' ᵗ) (inj₂ ((₀ , b1) , lm)) ((ZM x) ↑ • CZ)) .proj₂ ≡
             ((ract'' ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ^ (x ^1) • (ZM x) ↑)) .proj₂
    coset≡ = Eq.trans (lift-inner₂ (₀ , b1) lm (ZM x) CZ)
      (Eq.trans (Eq.cong (λ c → ((ract'' ᵗ) (inj₂ ((₀ , b1) , c)) CZ) .proj₂)
          ifix)
      (Eq.trans
        (Eq.cong₂ (λ v w → inj₂ ((₀ , v) , inj₂ ((₁₊ w2' , w) , lm2)))
          bfix
          (Eq.trans (Eq.cong (g₂' +_) -0#≈0#) (+-identityʳ g₂')))
      (Eq.sym (Eq.trans
        (Eq.cong (λ c → ((ract'' ᵗ) c ((ZM x) ↑)) .proj₂) cSfix)
        (Eq.trans (lift-last₂ (₀ , b₃) lm (ZM x))
          (Eq.cong (λ c → inj₂ ((₀ , b₃) , c)) ifix))))))

  semiMuCZ-go-a0 : ∀ (x : ℤ* ₚ) (xs' a1 : Fin (₁₊ p-2))
    (b1 g2 g₂' g₃ : ℤ ₚ) (lm2 : C (₁₊ m)) →
    x .proj₁ ≡ ₁₊ xs' →
    (x ⁻¹) .proj₁ * g2 ≡ g₂' →
    g2 + nsum (toℕ (x .proj₁)) (- ₁₊ a1) ≡ g₃ →
    ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , inj₂ ((₀ , g2) , lm2))) ((ZM x) ↑ • CZ)) ≋
    ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , inj₂ ((₀ , g2) , lm2)))
      (CZ^ (x ^1) • (ZM x) ↑))
  semiMuCZ-go-a0 x xs' a1 b1 g2 g₂' g₃ lm2 eq-x eq₂ eq-g = resid≈ , coset≡
    where
    xv = x .proj₁
    ixv = (x ⁻¹) .proj₁
    inst-x = nztoℕ {y = xv} {neq0 = x .proj₂}
    lm lmM lmG : C (₂₊ m)
    lm  = inj₂ ((₀ , g2) , lm2)
    lmM = inj₂ ((₀ , g₂') , lm2)
    lmG = inj₂ ((₀ , g₃) , lm2)

    ifix : ((ract {₁₊ m} ᵗ) lm (ZM x)) .proj₂ ≡ lmM
    ifix = Eq.trans (MD-coset!0 x g2 lm2)
             (Eq.cong (λ v → inj₂ ((₀ , v) , lm2)) eq₂)

    ifixG : ((ract {₁₊ m} ᵗ) lmG (ZM x)) .proj₂ ≡
            inj₂ ((₀ , ixv * g₃) , lm2)
    ifixG = MD-coset!0 x g₃ lm2

    cSfix : ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , lm)) (CZ ^ toℕ xv)) .proj₂ ≡
            inj₂ ((₁₊ a1 , b1) , lmG)
    cSfix = Eq.trans (ract-CZ^-coset (₁₊ a1 , b1) (₀ , g2) lm2 (toℕ xv))
      (Eq.cong₂ (λ v w → inj₂ ((₁₊ a1 , v) , inj₂ ((₀ , w) , lm2)))
        (Eq.trans (Eq.cong (b1 +_)
            (Eq.trans (nsum-neg xv ₀)
              (Eq.trans (Eq.cong -_ (*-zeroʳ xv)) -0#≈0#)))
          (+-identityʳ b1))
        eq-g)

    slide : (ZM x) ↑ • (H • (CZ • H ^ 3)) ≈
            (H • (CZ^ (x ^1) • H ^ 3)) • (ZM x) ↑
    slide = begin
      (ZM x) ↑ • (H • (CZ • H ^ 3))   ≈⟨ sym assoc ⟩
      ((ZM x) ↑ • H) • (CZ • H ^ 3)   ≈⟨ cleft (comm-Mup-H x) ⟩
      (H • (ZM x) ↑) • (CZ • H ^ 3)   ≈⟨ assoc ⟩
      H • ((ZM x) ↑ • (CZ • H ^ 3))   ≈⟨ cright (sym assoc) ⟩
      H • (((ZM x) ↑ • CZ) • H ^ 3)   ≈⟨ cright (cleft (MCZ-slide-↑ x)) ⟩
      H • ((CZ^ (x ^1) • (ZM x) ↑) • H ^ 3)   ≈⟨ cright assoc ⟩
      H • (CZ^ (x ^1) • ((ZM x) ↑ • H ^ 3))   ≈⟨ cright (cright (comm-Mup-H3 x)) ⟩
      H • (CZ^ (x ^1) • (H ^ 3 • (ZM x) ↑))   ≈⟨ cright (sym assoc) ⟩
      H • ((CZ^ (x ^1) • H ^ 3) • (ZM x) ↑)   ≈⟨ sym assoc ⟩
      (H • (CZ^ (x ^1) • H ^ 3)) • (ZM x) ↑ ∎

    Wpow : (H • (CZ • H ^ 3)) ^ toℕ xv ≈ H • (CZ^ (x ^1) • H ^ 3)
    Wpow =
      trans (refl' (Eq.cong (λ t → (H • (CZ • H ^ 3)) ^ toℕ t) eq-x))
      (trans (conj-pow H CZ (H ^ 3) (toℕ xs') (H3H≈ε {₁₊ m}))
        (refl' (Eq.cong (λ t → H • ((CZ ^ toℕ t) • H ^ 3))
          (Eq.sym eq-x))))

    resid≈ : ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , lm)) ((ZM x) ↑ • CZ)) .proj₁ ≈
             ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , lm)) (CZ^ (x ^1) • (ZM x) ↑)) .proj₁
    resid≈ =
      trans (refl' (Eq.trans (lift-inner (₁₊ a1 , b1) lm (ZM x) CZ)
        (Eq.cong (λ c → (_↑ (((ract {₁₊ m} ᵗ) lm (ZM x)) .proj₁)) •
            ((ract'' ᵗ) c CZ) .proj₁)
          (Eq.cong (λ c' → inj₂ ((₁₊ a1 , b1) , c')) ifix))))
      (trans (cong (lemma-cong↑ (((ract {₁₊ m} ᵗ) lm (ZM x)) .proj₁) (ZM x)
               (MD-resid!0 x g2 lm2)) refl)
      (trans slide
      (sym (trans (cong (ract-CZ^-resid (₁₊ a1 , b1) (₀ , g2) lm2 (toℕ xv))
             (refl' (Eq.trans
               (Eq.cong (λ c → ((ract'' ᵗ) c ((ZM x) ↑)) .proj₁) cSfix)
               (lift-last (₁₊ a1 , b1) lmG (ZM x)))))
           (cong Wpow (lemma-cong↑ (((ract {₁₊ m} ᵗ) lmG (ZM x)) .proj₁)
             (ZM x) (MD-resid!0 x g₃ lm2)))))))

    gfix : g₂' + - ₁₊ a1 ≡ ixv * g₃
    gfix = Eq.sym (Eq.trans (Eq.cong (ixv *_) (Eq.sym eq-g))
      (Eq.trans (Eq.cong (ixv *_)
          (Eq.cong (g2 +_) (nsum-neg xv (₁₊ a1))))
      (Eq.trans (*-distribˡ-+ ixv g2 (- (xv * ₁₊ a1)))
        (Eq.cong₂ _+_ eq₂
          (Eq.trans (Eq.sym (-‿distribʳ-* ixv (xv * ₁₊ a1)))
            (Eq.cong -_
              (Eq.trans (Eq.sym (*-assoc ixv xv (₁₊ a1)))
              (Eq.trans (Eq.cong (_* ₁₊ a1) (lemma-⁻¹ˡ xv {{inst-x}}))
                        (*-identityˡ (₁₊ a1))))))))))

    coset≡ : ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , lm)) ((ZM x) ↑ • CZ)) .proj₂ ≡
             ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , lm)) (CZ^ (x ^1) • (ZM x) ↑)) .proj₂
    coset≡ = Eq.trans (lift-inner₂ (₁₊ a1 , b1) lm (ZM x) CZ)
      (Eq.trans (Eq.cong (λ c → ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , c)) CZ) .proj₂)
          ifix)
      (Eq.trans
        (Eq.cong₂ (λ v w → inj₂ ((₁₊ a1 , v) , inj₂ ((₀ , w) , lm2)))
          (Eq.trans (Eq.cong (b1 +_) -0#≈0#) (+-identityʳ b1))
          gfix)
      (Eq.sym (Eq.trans
        (Eq.cong (λ c → ((ract'' ᵗ) c ((ZM x) ↑)) .proj₂) cSfix)
        (Eq.trans (lift-last₂ (₁₊ a1 , b1) lmG (ZM x))
          (Eq.cong (λ c → inj₂ ((₁₊ a1 , b1) , c)) ifixG))))))

  semiMuCZ-go-cc : ∀ (x : ℤ* ₚ) (xs' a1 c2 w2' : Fin (₁₊ p-2))
    (b1 g2 g₂' b₃ g₃ : ℤ ₚ) (lm2 : C (₁₊ m)) →
    x .proj₁ ≡ ₁₊ xs' →
    x .proj₁ * ₁₊ c2 ≡ ₁₊ w2' →
    (x ⁻¹) .proj₁ * g2 ≡ g₂' →
    b1 + nsum (toℕ (x .proj₁)) (- ₁₊ c2) ≡ b₃ →
    g2 + nsum (toℕ (x .proj₁)) (- ₁₊ a1) ≡ g₃ →
    ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , inj₂ ((₁₊ c2 , g2) , lm2)))
      ((ZM x) ↑ • CZ)) ≋
    ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , inj₂ ((₁₊ c2 , g2) , lm2)))
      (CZ^ (x ^1) • (ZM x) ↑))
  semiMuCZ-go-cc x xs' a1 c2 w2' b1 g2 g₂' b₃ g₃ lm2 eq-x eq-w eq₂ eq₃ eq-g =
    resid≈ , coset≡
    where
    xv = x .proj₁
    ixv = (x ⁻¹) .proj₁
    inst-x = nztoℕ {y = xv} {neq0 = x .proj₂}
    lm lmM lmG lmGM : C (₂₊ m)
    lm   = inj₂ ((₁₊ c2 , g2) , lm2)
    lmM  = inj₂ ((₁₊ w2' , g₂') , lm2)
    lmG  = inj₂ ((₁₊ c2 , g₃) , lm2)
    lmGM = inj₂ ((₁₊ w2' , ixv * g₃) , lm2)

    iA1 = ((₁₊ a1 , λ ()) ⁻¹) .proj₁
    iC2 = ((₁₊ c2 , λ ()) ⁻¹) .proj₁
    iW2 = ((₁₊ w2' , λ ()) ⁻¹) .proj₁

    u  = - ₁₊ c2 * iA1
    v  = - ₁₊ a1 * iC2
    u' = - ₁₊ w2' * iA1
    v' = - ₁₊ a1 * iW2
    sv = v' * (xv * xv)

    padW : ∀ (A C : Fin (₁₊ p-2)) (B G : ℤ ₚ) →
      (DDCZ.dir-of ((₁₊ A , B) ∷ (₁₊ C , G) ∷ []) ↓ᵏ m) ≡
      H • (H ↑ • (CZ • (S^ (- ₁₊ C * ((₁₊ A , λ ()) ⁻¹) .proj₁) •
        (H ^ 3 • (S^ (- ₁₊ A * ((₁₊ C , λ ()) ⁻¹) .proj₁) ↑ • (H ↑) ^ 3)))))
    padW A C B G = Eq.cong₂
      (λ s t → H • (H ↑ • (CZ • (s • (H ^ 3 • (t • (H ↑) ^ 3))))))
      (S^-↓ᵏ (- ₁₊ C * ((₁₊ A , λ ()) ⁻¹) .proj₁) m)
      (Eq.trans (↑↓ᵏ-comm (S^ (- ₁₊ A * ((₁₊ C , λ ()) ⁻¹) .proj₁)) m)
        (Eq.cong _↑ (S^-↓ᵏ (- ₁₊ A * ((₁₊ C , λ ()) ⁻¹) .proj₁) m)))

    ifix : ((ract {₁₊ m} ᵗ) lm (ZM x)) .proj₂ ≡ lmM
    ifix = Eq.trans (MD-coset!+ x c2 g2 lm2)
             (Eq.cong₂ (λ p₁ q₁ → inj₂ ((p₁ , q₁) , lm2)) eq-w eq₂)

    ifixG : ((ract {₁₊ m} ᵗ) lmG (ZM x)) .proj₂ ≡ lmGM
    ifixG = Eq.trans (MD-coset!+ x c2 g₃ lm2)
              (Eq.cong (λ p₁ → inj₂ ((p₁ , ixv * g₃) , lm2)) eq-w)

    cSfix : ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , lm)) (CZ ^ toℕ xv)) .proj₂ ≡
            inj₂ ((₁₊ a1 , b₃) , lmG)
    cSfix = Eq.trans (ract-CZ^-coset (₁₊ a1 , b1) (₁₊ c2 , g2) lm2 (toℕ xv))
      (Eq.cong₂ (λ p₁ q₁ → inj₂ ((₁₊ a1 , p₁) , inj₂ ((₁₊ c2 , q₁) , lm2)))
        eq₃ eq-g)

    slide : (ZM (x ⁻¹)) ↑ •
        (H • (H ↑ • (CZ • (S^ u' • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3)))))) ≈
      (H • (H ↑ • (CZ^ (x ^1) • (S^ u' • (H ^ 3 • (S^ sv ↑ • (H ↑) ^ 3)))))) •
        (ZM (x ⁻¹)) ↑
    slide = begin
      (ZM (x ⁻¹)) ↑ • (H • (H ↑ • (CZ • (S^ u' • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3))))))
        ≈⟨ sym assoc ⟩
      ((ZM (x ⁻¹)) ↑ • H) • (H ↑ • (CZ • (S^ u' • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3)))))
        ≈⟨ cleft (comm-Mup-H (x ⁻¹)) ⟩
      (H • (ZM (x ⁻¹)) ↑) • (H ↑ • (CZ • (S^ u' • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3)))))
        ≈⟨ assoc ⟩
      H • ((ZM (x ⁻¹)) ↑ • (H ↑ • (CZ • (S^ u' • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3))))))
        ≈⟨ cright (sym assoc) ⟩
      H • (((ZM (x ⁻¹)) ↑ • H ↑) • (CZ • (S^ u' • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3)))))
        ≈⟨ cright (cleft (swapfix-↑ x)) ⟩
      H • ((H ↑ • (ZM x) ↑) • (CZ • (S^ u' • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3)))))
        ≈⟨ cright assoc ⟩
      H • (H ↑ • ((ZM x) ↑ • (CZ • (S^ u' • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3))))))
        ≈⟨ cright (cright (sym assoc)) ⟩
      H • (H ↑ • (((ZM x) ↑ • CZ) • (S^ u' • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3)))))
        ≈⟨ cright (cright (cleft (MCZ-slide-↑ x))) ⟩
      H • (H ↑ • ((CZ^ (x ^1) • (ZM x) ↑) • (S^ u' • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3)))))
        ≈⟨ cright (cright assoc) ⟩
      H • (H ↑ • (CZ^ (x ^1) • ((ZM x) ↑ • (S^ u' • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3))))))
        ≈⟨ cright (cright (cright (sym assoc))) ⟩
      H • (H ↑ • (CZ^ (x ^1) • (((ZM x) ↑ • S^ u') • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3)))))
        ≈⟨ cright (cright (cright (cleft (comm-Mup-Spow x u')))) ⟩
      H • (H ↑ • (CZ^ (x ^1) • ((S^ u' • (ZM x) ↑) • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3)))))
        ≈⟨ cright (cright (cright assoc)) ⟩
      H • (H ↑ • (CZ^ (x ^1) • (S^ u' • ((ZM x) ↑ • (H ^ 3 • (S^ v' ↑ • (H ↑) ^ 3))))))
        ≈⟨ cright (cright (cright (cright (sym assoc)))) ⟩
      H • (H ↑ • (CZ^ (x ^1) • (S^ u' • (((ZM x) ↑ • H ^ 3) • (S^ v' ↑ • (H ↑) ^ 3)))))
        ≈⟨ cright (cright (cright (cright (cleft (comm-Mup-H3 x))))) ⟩
      H • (H ↑ • (CZ^ (x ^1) • (S^ u' • ((H ^ 3 • (ZM x) ↑) • (S^ v' ↑ • (H ↑) ^ 3)))))
        ≈⟨ cright (cright (cright (cright assoc))) ⟩
      H • (H ↑ • (CZ^ (x ^1) • (S^ u' • (H ^ 3 • ((ZM x) ↑ • (S^ v' ↑ • (H ↑) ^ 3))))))
        ≈⟨ cright (cright (cright (cright (cright (sym assoc))))) ⟩
      H • (H ↑ • (CZ^ (x ^1) • (S^ u' • (H ^ 3 • (((ZM x) ↑ • S^ v' ↑) • (H ↑) ^ 3)))))
        ≈⟨ cright (cright (cright (cright (cright (cleft (MS-slide-↑ x v')))))) ⟩
      H • (H ↑ • (CZ^ (x ^1) • (S^ u' • (H ^ 3 • ((S^ sv ↑ • (ZM x) ↑) • (H ↑) ^ 3)))))
        ≈⟨ cright (cright (cright (cright (cright assoc)))) ⟩
      H • (H ↑ • (CZ^ (x ^1) • (S^ u' • (H ^ 3 • (S^ sv ↑ • ((ZM x) ↑ • (H ↑) ^ 3))))))
        ≈⟨ cright (cright (cright (cright (cright (cright (M-H3-↑ x)))))) ⟩
      H • (H ↑ • (CZ^ (x ^1) • (S^ u' • (H ^ 3 • (S^ sv ↑ • ((H ↑) ^ 3 • (ZM (x ⁻¹)) ↑))))))
        ≈⟨ cright (cright (cright (cright (cright (sym assoc))))) ⟩
      H • (H ↑ • (CZ^ (x ^1) • (S^ u' • (H ^ 3 • ((S^ sv ↑ • (H ↑) ^ 3) • (ZM (x ⁻¹)) ↑)))))
        ≈⟨ cright (cright (cright (cright (sym assoc)))) ⟩
      H • (H ↑ • (CZ^ (x ^1) • (S^ u' • ((H ^ 3 • (S^ sv ↑ • (H ↑) ^ 3)) • (ZM (x ⁻¹)) ↑))))
        ≈⟨ cright (cright (cright (sym assoc))) ⟩
      H • (H ↑ • (CZ^ (x ^1) • ((S^ u' • (H ^ 3 • (S^ sv ↑ • (H ↑) ^ 3))) • (ZM (x ⁻¹)) ↑)))
        ≈⟨ cright (cright (sym assoc)) ⟩
      H • (H ↑ • ((CZ^ (x ^1) • (S^ u' • (H ^ 3 • (S^ sv ↑ • (H ↑) ^ 3)))) • (ZM (x ⁻¹)) ↑))
        ≈⟨ cright (sym assoc) ⟩
      H • ((H ↑ • (CZ^ (x ^1) • (S^ u' • (H ^ 3 • (S^ sv ↑ • (H ↑) ^ 3))))) • (ZM (x ⁻¹)) ↑)
        ≈⟨ sym assoc ⟩
      (H • (H ↑ • (CZ^ (x ^1) • (S^ u' • (H ^ 3 • (S^ sv ↑ • (H ↑) ^ 3)))))) • (ZM (x ⁻¹)) ↑ ∎

    iW2≡ : iW2 ≡ ixv * iC2
    iW2≡ = Eq.trans
      (inv-cong (₁₊ w2' , λ ()) (x *' (₁₊ c2 , λ ())) (Eq.sym eq-w))
      (inv-distrib x (₁₊ c2 , λ ()))

    uu' : u' ≡ xv * u
    uu' = Eq.trans (Eq.cong (λ t → - t * iA1) (Eq.sym eq-w))
      (Eq.trans (Eq.cong (_* iA1) (-‿distribʳ-* xv (₁₊ c2)))
        (*-assoc xv (- ₁₊ c2) iA1))

    vv' : sv ≡ xv * v
    vv' = Eq.trans (Eq.cong (λ t → (- ₁₊ a1 * t) * (xv * xv)) iW2≡)
      (Eq.trans (Eq.cong (_* (xv * xv)) (Eq.sym (*-assoc (- ₁₊ a1) ixv iC2)))
      (Eq.trans (*-assoc (- ₁₊ a1 * ixv) iC2 (xv * xv))
      (Eq.trans (Eq.cong ((- ₁₊ a1 * ixv) *_) (Eq.sym (*-assoc iC2 xv xv)))
      (Eq.trans (Eq.sym (*-assoc (- ₁₊ a1 * ixv) (iC2 * xv) xv))
      (Eq.trans (Eq.cong (_* xv)
          (Eq.trans (*-assoc (- ₁₊ a1) ixv (iC2 * xv))
            (Eq.cong ((- ₁₊ a1) *_)
              (Eq.trans (Eq.cong (ixv *_) (*-comm iC2 xv))
              (Eq.trans (Eq.sym (*-assoc ixv xv iC2))
              (Eq.trans (Eq.cong (_* iC2) (lemma-⁻¹ˡ xv {{inst-x}}))
                        (*-identityˡ iC2)))))))
        (*-comm (- ₁₊ a1 * iC2) xv))))))

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
             (toℕ xs') (QPcc {m}) ⟩
      (H • H ↑) • ((CZ • (S^ u • S^ v ↑)) ^ (₁₊ (toℕ xs')) • (H ^ 3 • (H ↑) ^ 3))
        ≈⟨ cright (cleft (refl' (Eq.cong (λ t → (CZ • (S^ u • S^ v ↑)) ^ toℕ t)
             (Eq.sym eq-x)))) ⟩
      (H • H ↑) • ((CZ • (S^ u • S^ v ↑)) ^ toℕ xv • (H ^ 3 • (H ↑) ^ 3))
        ≈⟨ cright (cleft (Cx-pow {m} xv u v)) ⟩
      (H • H ↑) • (((CZ ^ toℕ xv) • (S^ (xv * u) • S^ (xv * v) ↑)) • (H ^ 3 • (H ↑) ^ 3)) ∎

    resid≈ : ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , lm)) ((ZM x) ↑ • CZ)) .proj₁ ≈
             ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , lm)) (CZ^ (x ^1) • (ZM x) ↑)) .proj₁
    resid≈ =
      trans (refl' (Eq.trans (lift-inner (₁₊ a1 , b1) lm (ZM x) CZ)
        (Eq.trans
          (Eq.cong (λ c → (_↑ (((ract {₁₊ m} ᵗ) lm (ZM x)) .proj₁)) •
              ((ract'' ᵗ) c CZ) .proj₁)
            (Eq.cong (λ c' → inj₂ ((₁₊ a1 , b1) , c')) ifix))
          (Eq.cong ((_↑ (((ract {₁₊ m} ᵗ) lm (ZM x)) .proj₁)) •_)
            (padW a1 w2' b1 g₂')))))
      (trans (cong (lemma-cong↑ (((ract {₁₊ m} ᵗ) lm (ZM x)) .proj₁) (ZM (x ⁻¹))
               (MD-resid!+ x c2 g2 lm2)) refl)
      (trans slide
      (trans (cong (refl' (Eq.cong
          (λ t → H • (H ↑ • (CZ^ (x ^1) • (S^ t • (H ^ 3 • (S^ sv ↑ • (H ↑) ^ 3))))))
          uu')) refl)
      (trans (cong (refl' (Eq.cong
          (λ t → H • (H ↑ • (CZ^ (x ^1) • (S^ (xv * u) • (H ^ 3 • (S^ t ↑ • (H ↑) ^ 3))))))
          vv')) refl)
      (trans (cong (reshape (CZ^ (x ^1)) (xv * u) (xv * v)) refl)
      (sym (trans (cong (ract-CZ^-resid (₁₊ a1 , b1) (₁₊ c2 , g2) lm2 (toℕ xv))
             (refl' (Eq.trans
               (Eq.cong (λ c → ((ract'' ᵗ) c ((ZM x) ↑)) .proj₁) cSfix)
               (lift-last (₁₊ a1 , b₃) lmG (ZM x)))))
           (cong Wpow (lemma-cong↑ (((ract {₁₊ m} ᵗ) lmG (ZM x)) .proj₁)
             (ZM (x ⁻¹)) (MD-resid!+ x c2 g₃ lm2))))))))))

    bfix : b1 + - ₁₊ w2' ≡ b₃
    bfix = Eq.trans
      (Eq.cong (λ t → b1 + - t) (Eq.sym eq-w))
      (Eq.trans (Eq.cong (b1 +_) (Eq.sym (nsum-neg xv (₁₊ c2)))) eq₃)

    gfix : g₂' + - ₁₊ a1 ≡ ixv * g₃
    gfix = Eq.sym (Eq.trans (Eq.cong (ixv *_) (Eq.sym eq-g))
      (Eq.trans (Eq.cong (ixv *_)
          (Eq.cong (g2 +_) (nsum-neg xv (₁₊ a1))))
      (Eq.trans (*-distribˡ-+ ixv g2 (- (xv * ₁₊ a1)))
        (Eq.cong₂ _+_ eq₂
          (Eq.trans (Eq.sym (-‿distribʳ-* ixv (xv * ₁₊ a1)))
            (Eq.cong -_
              (Eq.trans (Eq.sym (*-assoc ixv xv (₁₊ a1)))
              (Eq.trans (Eq.cong (_* ₁₊ a1) (lemma-⁻¹ˡ xv {{inst-x}}))
                        (*-identityˡ (₁₊ a1))))))))))

    coset≡ : ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , lm)) ((ZM x) ↑ • CZ)) .proj₂ ≡
             ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , lm)) (CZ^ (x ^1) • (ZM x) ↑)) .proj₂
    coset≡ = Eq.trans (lift-inner₂ (₁₊ a1 , b1) lm (ZM x) CZ)
      (Eq.trans (Eq.cong (λ c → ((ract'' ᵗ) (inj₂ ((₁₊ a1 , b1) , c)) CZ) .proj₂)
          ifix)
      (Eq.trans
        (Eq.cong₂ (λ p₁ q₁ → inj₂ ((₁₊ a1 , p₁) , inj₂ ((₁₊ w2' , q₁) , lm2)))
          bfix gfix)
      (Eq.sym (Eq.trans
        (Eq.cong (λ c → ((ract'' ᵗ) c ((ZM x) ↑)) .proj₂) cSfix)
        (Eq.trans (lift-last₂ (₁₊ a1 , b₃) lmG (ZM x))
          (Eq.cong (λ c → inj₂ ((₁₊ a1 , b₃) , c)) ifixG))))))
