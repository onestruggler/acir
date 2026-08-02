------------------------------------------------------------------------
-- Presentations of groups
--
-- selinger-c10 cases of srel-wd on doubly-inj₂ cosets.  S⁻¹ = S ^ p-1
-- threads through the box pair with the S^-engines (k := p-1), the
-- lifted letters via ract-↑-≡, and the residual is the axiom.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10
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
  using (-0#≈0# ; -‿involutive)

import Examples.Groups.Symplectic.BR.Three.DD-CZ p-2 p-prime as DDCZ
open import Examples.Groups.Symplectic.Normalization.Pushing.DVecPush p-2 p-prime
  using (Hdir ; Hd')
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ p-2 p-prime
  using (↓-pow-S)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ2 p-2 p-prime
  using (ract-↑-≡)

------------------------------------------------------------------------
-- Summing p-1 copies negates: nsum (p-1) x ≡ - x.

nsum-p-1 : ∀ (x : ℤ ₚ) → nsum p-1 x ≡ - x
nsum-p-1 x = Eq.trans (Eq.sym (+-0ˡ (nsum p-1 x)))
  (Eq.trans (Eq.cong (_+ nsum p-1 x) (Eq.sym (+-inverseˡ x)))
  (Eq.trans (+-assoc (- x) x (nsum p-1 x))
  (Eq.trans (Eq.cong (- x +_) (nsum-p≡0 x))
            (+-identityʳ (- x)))))

------------------------------------------------------------------------
-- c10 on a doubly-inj₂ coset, both boxes (₀,·) with zero d2: every
-- escape is the corresponding letter and the residual is the axiom.

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)

  private
    ract2 = ract {₂₊ m}

  c10-go-000 : ∀ (b1 : ℤ ₚ) (lm2 : C (₁₊ m)) →
    ((ract2 ᵗ) (inj₂ ((₀ , b1) , inj₂ ((₀ , ₀) , lm2)))
      (CZ • H ↑ • CZ)) ≋
    ((ract2 ᵗ) (inj₂ ((₀ , b1) , inj₂ ((₀ , ₀) , lm2)))
      (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓))
  c10-go-000 b1 lm2 = resid≈ , coset≡
    where
    e0 : ∀ (t : ℤ ₚ) → t + - ₀ ≡ t
    e0 t = Eq.trans (Eq.cong (t +_) -0#≈0#) (+-identityʳ t)

    z00 : - ₀ + - ₀ ≡ ₀
    z00 = Eq.trans (Eq.cong₂ _+_ -0#≈0# -0#≈0#) (+-identityʳ ₀)

    lm : C (₂₊ m)
    lm = inj₂ ((₀ , ₀) , lm2)

    -- LHS: rewrite the two stuck slots, then the residual is literal.
    resid-L : ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ • H ↑ • CZ)) .proj₁ ≈
              CZ • (H ↑ • CZ)
    resid-L = refl' (Eq.cong₂ _•_ Eq.refl (Eq.cong₂ _•_
      (Eq.cong (λ v → (Hdir (₀ , v) ↓ᵏ m) ↑) (e0 ₀))
      (Eq.cong (λ pr → ((ract2 ᵗ) pr CZ) .proj₁)
        (Eq.cong₂ (λ v w → inj₂ ((₀ , b1 + - ₀) , inj₂ ((v , w) , lm2)))
          (e0 ₀) -0#≈0#))))

    -- RHS: seven letters, four of them S⁻¹-chunks driven by the
    -- S^-engines at k = p-1.
    r1 : ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm)) (S⁻¹ ↑)) ≡
         ((S ^ p-1) ↑ , inj₂ ((₀ , b1) , lm))
    r1 = Eq.trans (ract-↑-≡ (₀ , b1) lm S⁻¹)
      (Eq.cong₂ _,_
        (Eq.cong _↑ (ract-S^-resid-a0 ₀ lm2 p-1))
        (Eq.cong (λ c → inj₂ ((₀ , b1) , c))
          (Eq.trans (ract-S^-coset (₀ , ₀) lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2)) (it-dDS-a0 p-1 ₀)))))

    resid≈ : ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ • H ↑ • CZ)) .proj₁ ≈
             ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm))
               (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₁
    resid≈ =
      trans resid-L
      (trans (axiom selinger-c10)
      (sym (refl' R-fix)))
      where
      REST5 = H ↑ • S⁻¹ ↑ • S⁻¹ ↓
      R-fix : ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm))
                (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₁ ≡
              S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • S⁻¹ ↓)))))
      R-fix =
        Eq.trans (Eq.cong
            (λ pr → pr .proj₁ •
              ((ract2 ᵗ) (pr .proj₂) (H ↑ • S⁻¹ ↑ • CZ • REST5)) .proj₁)
            r1)
        (Eq.cong ((S ^ p-1) ↑ •_)
        (Eq.cong (λ t → (Hdir (₀ , ₀) ↓ᵏ m) ↑ • t)
        (Eq.trans (Eq.cong
            (λ pr → pr .proj₁ •
              ((ract2 ᵗ) (pr .proj₂) (CZ • REST5)) .proj₁)
            (Eq.trans (ract-↑-≡ (₀ , b1) (inj₂ ((₀ , - ₀) , lm2)) S⁻¹)
              (Eq.cong₂ _,_
                (Eq.cong _↑ (ract-S^-resid-a0 (- ₀) lm2 p-1))
                (Eq.cong (λ c → inj₂ ((₀ , b1) , c))
                  (Eq.trans (ract-S^-coset (₀ , - ₀) lm2 p-1)
                    (Eq.cong (λ d → inj₂ (d , lm2)) (it-dDS-a0 p-1 (- ₀))))))))
        (Eq.cong ((S ^ p-1) ↑ •_)
        (Eq.cong (λ t → CZ • t)
        (Eq.trans (Eq.cong
            (λ pr → pr .proj₁ • ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↑ • S⁻¹ ↓)) .proj₁)
            (Eq.cong (λ v → ((Hdir (₀ , v) ↓ᵏ m) ↑ ,
                inj₂ ((₀ , b1 + - ₀) , inj₂ (Hd' (₀ , v) , lm2)))) z00))
        (Eq.cong (λ t → (Hdir (₀ , ₀) ↓ᵏ m) ↑ • t)
        (Eq.trans (Eq.cong
            (λ pr → pr .proj₁ • ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↓)) .proj₁)
            (Eq.trans (ract-↑-≡ (₀ , b1 + - ₀) (inj₂ ((₀ , - ₀) , lm2)) S⁻¹)
              (Eq.cong₂ _,_
                (Eq.cong _↑ (ract-S^-resid-a0 (- ₀) lm2 p-1))
                (Eq.cong (λ c → inj₂ ((₀ , b1 + - ₀) , c))
                  (Eq.trans (ract-S^-coset (₀ , - ₀) lm2 p-1)
                    (Eq.cong (λ d → inj₂ (d , lm2)) (it-dDS-a0 p-1 (- ₀))))))))
        (Eq.cong ((S ^ p-1) ↑ •_)
          (Eq.trans (Eq.cong (λ w → ((ract2 ᵗ)
              (inj₂ ((₀ , b1 + - ₀) , inj₂ ((₀ , - ₀) , lm2))) w) .proj₁)
              (↓-pow-S p-1))
            (ract-S^-resid-a0 (b1 + - ₀)
              (inj₂ ((₀ , - ₀) , lm2)) p-1)))))))))))

    coset≡ : ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ • H ↑ • CZ)) .proj₂ ≡
             ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm))
               (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₂
    coset≡ = Eq.trans L-c (Eq.sym R-c)
      where
      REST5 = H ↑ • S⁻¹ ↑ • S⁻¹ ↓

      L-c : ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ • H ↑ • CZ)) .proj₂ ≡
            inj₂ ((₀ , b1) , inj₂ ((₀ , ₀) , lm2))
      L-c = Eq.trans (Eq.cong (λ pr → ((ract2 ᵗ) pr CZ) .proj₂)
          (Eq.cong₂ (λ v w → inj₂ ((₀ , b1 + - ₀) , inj₂ ((v , w) , lm2)))
            (e0 ₀) -0#≈0#))
        (Eq.cong₂ (λ v w → inj₂ ((₀ , v) , w))
          (Eq.trans (Eq.cong ((b1 + - ₀) +_) -0#≈0#)
            (Eq.trans (+-identityʳ (b1 + - ₀)) (e0 b1)))
          (Eq.cong (λ w → inj₂ ((₀ , w) , lm2)) (e0 ₀)))

      R-c : ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm))
              (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₂ ≡
            inj₂ ((₀ , b1) , inj₂ ((₀ , ₀) , lm2))
      R-c =
        Eq.trans (Eq.cong
            (λ pr → ((ract2 ᵗ) (pr .proj₂) (H ↑ • S⁻¹ ↑ • CZ • REST5)) .proj₂)
            r1)
        (Eq.trans (Eq.cong
            (λ pr → ((ract2 ᵗ) (pr .proj₂) (CZ • REST5)) .proj₂)
            (Eq.trans (ract-↑-≡ (₀ , b1) (inj₂ ((₀ , - ₀) , lm2)) S⁻¹)
              (Eq.cong₂ _,_ Eq.refl
                (Eq.cong (λ c → inj₂ ((₀ , b1) , c))
                  (Eq.trans (ract-S^-coset (₀ , - ₀) lm2 p-1)
                    (Eq.cong (λ d → inj₂ (d , lm2)) (it-dDS-a0 p-1 (- ₀))))))))
        (Eq.trans (Eq.cong
            (λ pr → ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↑ • S⁻¹ ↓)) .proj₂)
            (Eq.cong (λ v → ((Hdir (₀ , v) ↓ᵏ m) ↑ ,
                inj₂ ((₀ , b1 + - ₀) , inj₂ (Hd' (₀ , v) , lm2)))) z00))
        (Eq.trans (Eq.cong
            (λ pr → ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↓)) .proj₂)
            (Eq.trans (ract-↑-≡ (₀ , b1 + - ₀) (inj₂ ((₀ , - ₀) , lm2)) S⁻¹)
              (Eq.cong₂ _,_ Eq.refl
                (Eq.cong (λ c → inj₂ ((₀ , b1 + - ₀) , c))
                  (Eq.trans (ract-S^-coset (₀ , - ₀) lm2 p-1)
                    (Eq.cong (λ d → inj₂ (d , lm2)) (it-dDS-a0 p-1 (- ₀))))))))
        (Eq.trans (Eq.cong (λ w → ((ract2 ᵗ)
              (inj₂ ((₀ , b1 + - ₀) , inj₂ ((₀ , - ₀) , lm2))) w) .proj₂)
            (↓-pow-S p-1))
        (Eq.trans (ract-S^-coset (₀ , b1 + - ₀) (inj₂ ((₀ , - ₀) , lm2)) p-1)
        (Eq.trans (Eq.cong (λ d → inj₂ (d , inj₂ ((₀ , - ₀) , lm2)))
            (it-dDS-a0 p-1 (b1 + - ₀)))
          (Eq.cong₂ (λ v w → inj₂ ((₀ , v) , inj₂ ((₀ , w) , lm2)))
            (e0 b1) -0#≈0#)))))))
