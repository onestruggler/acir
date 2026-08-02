------------------------------------------------------------------------
-- Presentations of groups
--
-- Selinger-relation cases of srel-wd on deep inj₂ cosets.  c12 on a
-- triply-inj₂ coset: the lifted CZ threads the lower box pair via
-- ract-↑-≡ and the escapes commute through the axiom.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (inj₁ ; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Data.Fin using (Fin ; toℕ)
open import Data.Vec using ([] ; _∷_)

open import Word.Base
import Presentation.Base as PB

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Algebra.Properties.Ring (+-*-ring p-2)
  using (-0#≈0#)

import Examples.Groups.Symplectic.BR.Three.DD-CZ p-2 p-prime as DDCZ
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ2 p-2 p-prime
  using (ract-↑-≡)

------------------------------------------------------------------------
-- c12 on a triply-inj₂ coset, all-zero a-slots: every escape is the
-- CZ letter itself and the residual is the axiom.

module _ {m : ℕ} where
  open PB ((₃₊ m) QRel,_===_)

  private
    ract3 = ract {₃₊ m}

  c12-go-000 : ∀ (b1 b2 b3 : ℤ ₚ) (lm3 : C (₁₊ m)) →
    ((ract3 ᵗ) (inj₂ ((₀ , b1) , inj₂ ((₀ , b2) , inj₂ ((₀ , b3) , lm3))))
      (CZ ↑ • CZ)) ≋
    ((ract3 ᵗ) (inj₂ ((₀ , b1) , inj₂ ((₀ , b2) , inj₂ ((₀ , b3) , lm3))))
      (CZ • CZ ↑))
  c12-go-000 b1 b2 b3 lm3 = resid≈ , coset≡
    where
    lm : C (₃₊ m)
    lm = inj₂ ((₀ , b2) , inj₂ ((₀ , b3) , lm3))

    e0 : ∀ (t : ℤ ₚ) → t + - ₀ ≡ t
    e0 t = Eq.trans (Eq.cong (t +_) -0#≈0#) (+-identityʳ t)

    resid≈ : ((ract3 ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ ↑ • CZ)) .proj₁ ≈
             ((ract3 ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ • CZ ↑)) .proj₁
    resid≈ =
      trans (refl' (Eq.cong
          (λ pr → pr .proj₁ • ((ract3 ᵗ) (pr .proj₂) CZ) .proj₁)
          (ract-↑-≡ (₀ , b1) lm CZ)))
      (trans (axiom selinger-c12)
      (sym (refl' (Eq.cong
          (λ pr → CZ • pr .proj₁)
          (ract-↑-≡ (₀ , b1 + - ₀)
            (inj₂ ((₀ , b2 + - ₀) , inj₂ ((₀ , b3) , lm3))) CZ)))))

    fix2 : ∀ (t3 : ℤ ₚ) →
      inj₂ ((₀ , b1 + - ₀) ,
        inj₂ ((₀ , (b2 + - ₀) + - ₀) , inj₂ ((₀ , t3 + - ₀) , lm3))) ≡
      inj₂ ((₀ , b1) , inj₂ ((₀ , b2) , inj₂ ((₀ , t3) , lm3)))
    fix2 t3 = Eq.cong₂
      (λ v w → inj₂ ((₀ , v) , w))
      (e0 b1)
      (Eq.cong₂ (λ v w → inj₂ ((₀ , v) , inj₂ ((₀ , w) , lm3)))
        (Eq.trans (e0 (b2 + - ₀)) (e0 b2))
        (e0 t3))

    coset≡ : ((ract3 ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ ↑ • CZ)) .proj₂ ≡
             ((ract3 ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ • CZ ↑)) .proj₂
    coset≡ =
      Eq.trans (Eq.cong (λ pr → ((ract3 ᵗ) (pr .proj₂) CZ) .proj₂)
          (ract-↑-≡ (₀ , b1) lm CZ))
      (Eq.trans (fix2 b3)
      (Eq.sym (Eq.trans (Eq.cong proj₂
          (ract-↑-≡ (₀ , b1 + - ₀)
            (inj₂ ((₀ , b2 + - ₀) , inj₂ ((₀ , b3) , lm3))) CZ))
        (fix2 b3))))
