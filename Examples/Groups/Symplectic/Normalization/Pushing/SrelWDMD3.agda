------------------------------------------------------------------------
-- Presentations of groups
--
-- The semi-MS inj₂ cases of srel-wd, assembled from the MD engine.
-- Computed coset values are generalised to variables with equation
-- hypotheses, as in SrelWDMD2.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMD3
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (inj₁ ; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; _≢_)
open import Data.Fin using (Fin ; toℕ)

open import Word.Base
import Presentation.Base as PB

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Algebra.Properties.Ring (+-*-ring p-2)
  using (-‿distribʳ-*)

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDM p-2 p-prime
  using (nsum-* ; nsum-neg)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDZM p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMD p-2 p-prime

module _ {m : ℕ} where
  open PB ((₁₊ m) QRel,_===_)

  private
    ract' = ract {₁₊ m}

  semiMS-wd-0 : ∀ (x : ℤ* ₚ) (b b₂ : ℤ ₚ) (lm : C (₁₊ m)) →
    (x ⁻¹) .proj₁ * b ≡ b₂ →
    ((ract' ᵗ) (inj₂ ((₀ , b) , lm)) (ZM x • S)) ≋
    ((ract' ᵗ) (inj₂ ((₀ , b) , lm)) (S^ (x ^2) • ZM x))
  semiMS-wd-0 x b b₂ lm eq₂ = resid≈ , coset≡
    where
    c₂fix : ((ract' ᵗ) (inj₂ ((₀ , b) , lm)) (ZM x)) .proj₂ ≡
            inj₂ ((₀ , b₂) , lm)
    c₂fix = Eq.trans (MD-coset!0 x b lm)
              (Eq.cong (λ v → inj₂ ((₀ , v) , lm)) eq₂)

    cSfix : ((ract' ᵗ) (inj₂ ((₀ , b) , lm)) (S^ (x ^2))) .proj₂ ≡
            inj₂ ((₀ , b) , lm)
    cSfix = Eq.trans (ract-S^-coset (₀ , b) lm (toℕ (x ^2)))
              (Eq.cong (λ d → inj₂ (d , lm)) (it-dDS-a0 (toℕ (x ^2)) b))

    R≈ : ((ract' ᵗ) (inj₂ ((₀ , b) , lm)) (S^ (x ^2) • ZM x)) .proj₁ ≈
         S^ (x ^2) • ZM x
    R≈ = trans (refl'ᵣ (Eq.cong₂ _•_
             (ract-S^-resid-a0 b lm (toℕ (x ^2)))
             (Eq.cong (λ c → ((ract' ᵗ) c (ZM x)) .proj₁) cSfix)))
           (cong refl (MD-resid!0 x b lm))

    resid≈ : ((ract' ᵗ) (inj₂ ((₀ , b) , lm)) (ZM x • S)) .proj₁ ≈
             ((ract' ᵗ) (inj₂ ((₀ , b) , lm)) (S^ (x ^2) • ZM x)) .proj₁
    resid≈ = trans (cong (MD-resid!0 x b lm)
               (refl'ᵣ (Eq.cong (λ c → ((ract' ᵗ) c S) .proj₁) c₂fix)))
             (trans (axiom (semi-MS x)) (sym R≈))

    coset≡ : ((ract' ᵗ) (inj₂ ((₀ , b) , lm)) (ZM x • S)) .proj₂ ≡
             ((ract' ᵗ) (inj₂ ((₀ , b) , lm)) (S^ (x ^2) • ZM x)) .proj₂
    coset≡ = Eq.trans
      (Eq.cong (λ c → ((ract' ᵗ) c S) .proj₂) c₂fix)
      (Eq.sym (Eq.trans
        (Eq.cong (λ c → ((ract' ᵗ) c (ZM x)) .proj₂) cSfix)
        c₂fix))

  semiMS-wd-+ : ∀ (x : ℤ* ₚ) (a' v' : Fin (₁₊ p-2)) (b b₂ b₃ : ℤ ₚ)
    (lm : C (₁₊ m)) →
    x .proj₁ * ₁₊ a' ≡ ₁₊ v' →
    (x ⁻¹) .proj₁ * b ≡ b₂ →
    b + nsum (toℕ (x ^2)) (- ₁₊ a') ≡ b₃ →
    ((ract' ᵗ) (inj₂ ((₁₊ a' , b) , lm)) (ZM x • S)) ≋
    ((ract' ᵗ) (inj₂ ((₁₊ a' , b) , lm)) (S^ (x ^2) • ZM x))
  semiMS-wd-+ x a' v' b b₂ b₃ lm eq-v eq₂ eq₃ = resid≈ , coset≡
    where
    inst-x = nztoℕ {y = x .proj₁} {neq0 = x .proj₂}

    c₂fix : ((ract' ᵗ) (inj₂ ((₁₊ a' , b) , lm)) (ZM x)) .proj₂ ≡
            inj₂ ((₁₊ v' , b₂) , lm)
    c₂fix = Eq.trans (MD-coset!+ x a' b lm)
              (Eq.cong₂ (λ u v → inj₂ ((u , v) , lm)) eq-v eq₂)

    cSfix : ((ract' ᵗ) (inj₂ ((₁₊ a' , b) , lm)) (S^ (x ^2))) .proj₂ ≡
            inj₂ ((₁₊ a' , b₃) , lm)
    cSfix = Eq.trans (ract-S^-coset (₁₊ a' , b) lm (toℕ (x ^2)))
              (Eq.cong (λ d → inj₂ (d , lm))
                (Eq.trans (it-dDS-nz (toℕ (x ^2)) (₁₊ a') b (λ ()))
                  (Eq.cong (₁₊ a' ,_) eq₃)))

    L≈ : ((ract' ᵗ) (inj₂ ((₁₊ a' , b) , lm)) (ZM x • S)) .proj₁ ≈
         ZM (x ⁻¹)
    L≈ = trans (cong (MD-resid!+ x a' b lm)
           (refl'ᵣ (Eq.cong (λ c → ((ract' ᵗ) c S) .proj₁) c₂fix)))
         right-unit

    R≈ : ((ract' ᵗ) (inj₂ ((₁₊ a' , b) , lm)) (S^ (x ^2) • ZM x)) .proj₁ ≈
         ZM (x ⁻¹)
    R≈ = trans (cong (ract-S^-resid-a+ (₁₊ a' , b) lm (toℕ (x ^2)) (λ ()))
           (trans (refl'ᵣ (Eq.cong (λ c → ((ract' ᵗ) c (ZM x)) .proj₁) cSfix))
                  (MD-resid!+ x a' b₃ lm)))
         left-unit

    resid≈ : ((ract' ᵗ) (inj₂ ((₁₊ a' , b) , lm)) (ZM x • S)) .proj₁ ≈
             ((ract' ᵗ) (inj₂ ((₁₊ a' , b) , lm)) (S^ (x ^2) • ZM x)) .proj₁
    resid≈ = trans L≈ (sym R≈)

    -- x⁻¹ · (b - x²·a) ≡ b₂ - x·a, i.e. the two b-slots agree.
    snd-g : b₂ + - ₁₊ v' ≡ (x ⁻¹) .proj₁ * b₃
    snd-g = Eq.sym (Eq.trans (Eq.cong ((x ⁻¹) .proj₁ *_) (Eq.sym eq₃))
      (Eq.trans (Eq.cong ((x ⁻¹) .proj₁ *_)
          (Eq.cong (b +_) (nsum-neg (x ^2) (₁₊ a'))))
      (Eq.trans (*-distribˡ-+ ((x ⁻¹) .proj₁) b (- ((x ^2) * ₁₊ a')))
        (Eq.cong₂ _+_ eq₂
          (Eq.trans (Eq.sym (-‿distribʳ-* ((x ⁻¹) .proj₁) ((x ^2) * ₁₊ a')))
            (Eq.cong -_
              (Eq.trans (Eq.sym (*-assoc ((x ⁻¹) .proj₁) (x ^2) (₁₊ a')))
              (Eq.trans (Eq.cong (_* ₁₊ a')
                  (Eq.trans (Eq.sym (*-assoc ((x ⁻¹) .proj₁) (x .proj₁) (x .proj₁)))
                  (Eq.trans (Eq.cong (_* x .proj₁) (lemma-⁻¹ˡ (x .proj₁) {{inst-x}}))
                            (*-identityˡ (x .proj₁)))))
                eq-v))))))))

    coset≡ : ((ract' ᵗ) (inj₂ ((₁₊ a' , b) , lm)) (ZM x • S)) .proj₂ ≡
             ((ract' ᵗ) (inj₂ ((₁₊ a' , b) , lm)) (S^ (x ^2) • ZM x)) .proj₂
    coset≡ = Eq.trans
      (Eq.cong (λ c → ((ract' ᵗ) c S) .proj₂) c₂fix)
      (Eq.trans (Eq.cong₂ (λ u v → inj₂ ((u , v) , lm)) (Eq.sym eq-v) snd-g)
        (Eq.sym (Eq.trans
          (Eq.cong (λ c → ((ract' ᵗ) c (ZM x)) .proj₂) cSfix)
          (MD-coset!+ x a' b₃ lm))))
