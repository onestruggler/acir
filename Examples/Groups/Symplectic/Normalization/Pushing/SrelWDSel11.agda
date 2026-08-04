------------------------------------------------------------------------
-- Presentations of groups
--
-- selinger-c11 cases of srel-wd on doubly-inj₂ cosets.  c11 is the
-- ↓/↑ mirror of c10: the H and the first three S⁻¹ act on the BOTTOM
-- box through the width-native engines (no lifting), and only the
-- final S⁻¹↑ touches the upper box.  This module does the all-zero
-- pattern, where every escape is the letter itself.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel11
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

open import Examples.Groups.Symplectic.Normalization.Pushing.DVecPush
  p-2 p-prime using (Hdir ; Hd')
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ
  p-2 p-prime using (↓-pow-S)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ2
  p-2 p-prime using (ract-↑-≡)

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)

  private
    ract2 = ract {₂₊ m}

  -- Both boxes clean: every CZ escapes as CZ, every bottom H as H and
  -- every S⁻¹ as S^(p-1), so the residual is the axiom itself.
  c11-go-000 : ∀ (b2 : ℤ ₚ) (lm2 : C (₁₊ m)) →
    ((ract2 ᵗ) (inj₂ ((₀ , ₀) , inj₂ ((₀ , b2) , lm2)))
      (CZ • H ↓ • CZ)) ≋
    ((ract2 ᵗ) (inj₂ ((₀ , ₀) , inj₂ ((₀ , b2) , lm2)))
      (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑))
  c11-go-000 b2 lm2 = resid≈ , coset≡
    where
    e0 : ∀ (t : ℤ ₚ) → t + - ₀ ≡ t
    e0 t = Eq.trans (Eq.cong (t +_) -0#≈0#) (+-identityʳ t)

    z00 : - ₀ + - ₀ ≡ ₀
    z00 = Eq.trans (Eq.cong₂ _+_ -0#≈0# -0#≈0#) (+-identityʳ ₀)

    lm : C (₂₊ m)
    lm = inj₂ ((₀ , b2) , lm2)

    cF : C (₃₊ m)
    cF = inj₂ ((₀ , ₀) , inj₂ ((₀ , b2) , lm2))

    -- LHS: the middle H is the bottom H on the (₀,₀) box.
    L-fix : ((ract2 ᵗ) (inj₂ ((₀ , ₀) , lm)) (CZ • H ↓ • CZ)) .proj₁ ≡
            CZ • (H • CZ)
    L-fix = Eq.cong₂ _•_ Eq.refl (Eq.cong₂ _•_
      (Eq.cong (λ v → Hdir (₀ , v) ↓ᵏ (₁₊ m)) (e0 ₀))
      (Eq.cong (λ pr → ((ract2 ᵗ) pr CZ) .proj₁)
        (Eq.cong₂ (λ v w → inj₂ ((v , - ₀) , inj₂ ((₀ , w) , lm2)))
          (e0 ₀) (e0 b2))))

    L-c : ((ract2 ᵗ) (inj₂ ((₀ , ₀) , lm)) (CZ • H ↓ • CZ)) .proj₂ ≡ cF
    L-c = Eq.trans (Eq.cong (λ pr → ((ract2 ᵗ) pr CZ) .proj₂)
        (Eq.cong₂ (λ v w → inj₂ ((v , - ₀) , inj₂ ((₀ , w) , lm2)))
          (e0 ₀) (e0 b2)))
      (Eq.cong₂ (λ v w → inj₂ ((₀ , v) , inj₂ ((₀ , w) , lm2)))
        z00 (e0 b2))

    REST5 = H ↓ • S⁻¹ ↓ • S⁻¹ ↑

    -- RHS: r1/r3/r6 are the a=0 S-engine, r2/r5 the bottom H, r4 the
    -- clean CZ and r7 the lifted S-power.
    r1 : ((ract2 ᵗ) (inj₂ ((₀ , ₀) , lm)) (S⁻¹ ↓)) ≡
         (S ^ p-1 , inj₂ ((₀ , ₀) , lm))
    r1 = Eq.trans
      (Eq.cong (λ w → (ract2 ᵗ) (inj₂ ((₀ , ₀) , lm)) w) (↓-pow-S p-1))
      (Eq.cong₂ _,_
        (ract-S^-resid-a0 ₀ lm p-1)
        (Eq.trans (ract-S^-coset (₀ , ₀) lm p-1)
          (Eq.cong (λ d → inj₂ (d , lm)) (it-dDS-a0 p-1 ₀))))

    r3 : ((ract2 ᵗ) (inj₂ ((₀ , - ₀) , lm)) (S⁻¹ ↓)) ≡
         (S ^ p-1 , inj₂ ((₀ , - ₀) , lm))
    r3 = Eq.trans
      (Eq.cong (λ w → (ract2 ᵗ) (inj₂ ((₀ , - ₀) , lm)) w) (↓-pow-S p-1))
      (Eq.cong₂ _,_
        (ract-S^-resid-a0 (- ₀) lm p-1)
        (Eq.trans (ract-S^-coset (₀ , - ₀) lm p-1)
          (Eq.cong (λ d → inj₂ (d , lm)) (it-dDS-a0 p-1 (- ₀)))))

    r6 : ((ract2 ᵗ) (inj₂ ((₀ , - ₀) ,
           inj₂ ((₀ , b2 + - ₀) , lm2))) (S⁻¹ ↓)) ≡
         (S ^ p-1 , inj₂ ((₀ , - ₀) , inj₂ ((₀ , b2 + - ₀) , lm2)))
    r6 = Eq.trans
      (Eq.cong (λ w → (ract2 ᵗ) (inj₂ ((₀ , - ₀) ,
          inj₂ ((₀ , b2 + - ₀) , lm2))) w) (↓-pow-S p-1))
      (Eq.cong₂ _,_
        (ract-S^-resid-a0 (- ₀) (inj₂ ((₀ , b2 + - ₀) , lm2)) p-1)
        (Eq.trans (ract-S^-coset (₀ , - ₀)
            (inj₂ ((₀ , b2 + - ₀) , lm2)) p-1)
          (Eq.cong (λ d → inj₂ (d , inj₂ ((₀ , b2 + - ₀) , lm2)))
            (it-dDS-a0 p-1 (- ₀)))))

    r7 : ((ract2 ᵗ) (inj₂ ((₀ , - ₀) ,
           inj₂ ((₀ , b2 + - ₀) , lm2))) (S⁻¹ ↑)) ≡
         ((S ^ p-1) ↑ , inj₂ ((₀ , - ₀) ,
           inj₂ ((₀ , b2 + - ₀) , lm2)))
    r7 = Eq.trans
      (ract-↑-≡ (₀ , - ₀) (inj₂ ((₀ , b2 + - ₀) , lm2)) S⁻¹)
      (Eq.cong₂ _,_
        (Eq.cong _↑ (ract-S^-resid-a0 (b2 + - ₀) lm2 p-1))
        (Eq.cong (λ c → inj₂ ((₀ , - ₀) , c))
          (Eq.trans (ract-S^-coset (₀ , b2 + - ₀) lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2))
              (it-dDS-a0 p-1 (b2 + - ₀))))))

    R-fix : ((ract2 ᵗ) (inj₂ ((₀ , ₀) , lm))
              (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₁ ≡
            S ^ p-1 • (H • (S ^ p-1 • (CZ • (H • (S ^ p-1 •
              (S ^ p-1) ↑)))))
    R-fix =
      Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract2 ᵗ) (pr .proj₂) (H ↓ • S⁻¹ ↓ • CZ • REST5)) .proj₁)
          r1)
      (Eq.cong (λ t → S ^ p-1 • t)
      (Eq.cong (λ t → (Hdir (₀ , ₀) ↓ᵏ (₁₊ m)) • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ • ((ract2 ᵗ) (pr .proj₂) (CZ • REST5)) .proj₁)
          r3)
      (Eq.cong (λ t → S ^ p-1 • t)
      (Eq.cong (λ t → CZ • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↓ • S⁻¹ ↑)) .proj₁)
          (Eq.cong (λ v → ((Hdir (₀ , v) ↓ᵏ (₁₊ m)) ,
              inj₂ (Hd' (₀ , v) , inj₂ ((₀ , b2 + - ₀) , lm2)))) z00))
      (Eq.cong (λ t → (Hdir (₀ , ₀) ↓ᵏ (₁₊ m)) • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ • ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↑)) .proj₁)
          r6)
        (Eq.cong (λ t → S ^ p-1 • t) (Eq.cong proj₁ r7))))))))))

    resid≈ : ((ract2 ᵗ) (inj₂ ((₀ , ₀) , lm)) (CZ • H ↓ • CZ)) .proj₁ ≈
             ((ract2 ᵗ) (inj₂ ((₀ , ₀) , lm))
               (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₁
    resid≈ =
      trans (refl' L-fix)
      (trans (axiom selinger-c11)
      (sym (refl' R-fix)))

    R-c : ((ract2 ᵗ) (inj₂ ((₀ , ₀) , lm))
            (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₂ ≡ cF
    R-c =
      Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (H ↓ • S⁻¹ ↓ • CZ • REST5)) .proj₂)
          r1)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (CZ • REST5)) .proj₂)
          r3)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↓ • S⁻¹ ↑)) .proj₂)
          (Eq.cong (λ v → ((Hdir (₀ , v) ↓ᵏ (₁₊ m)) ,
              inj₂ (Hd' (₀ , v) , inj₂ ((₀ , b2 + - ₀) , lm2)))) z00))
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↑)) .proj₂)
          r6)
      (Eq.trans (Eq.cong proj₂ r7)
        (Eq.cong₂ (λ v w → inj₂ ((₀ , v) , inj₂ ((₀ , w) , lm2)))
          -0#≈0# (e0 b2))))))

    coset≡ : ((ract2 ᵗ) (inj₂ ((₀ , ₀) , lm)) (CZ • H ↓ • CZ)) .proj₂ ≡
             ((ract2 ᵗ) (inj₂ ((₀ , ₀) , lm))
               (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₂
    coset≡ = Eq.trans L-c (Eq.sym R-c)
