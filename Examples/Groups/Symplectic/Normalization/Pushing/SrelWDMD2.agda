------------------------------------------------------------------------
-- Presentations of groups
--
-- The M-mul inj₂ cases of srel-wd, assembled from the MD engine.  All
-- computed coset values are generalised to variables with equation
-- hypotheses (instantiated with Eq.refl at the dispatcher), so the
-- traversal types stay variable-only and conversion checking is cheap.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMD2
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

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDZM p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMD p-2 p-prime

module _ {m : ℕ} where
  open PB ((₁₊ m) QRel,_===_)

  private
    ract' = ract {₁₊ m}

  Mmul-wd-0 : ∀ (x y : ℤ* ₚ) (b b₂ : ℤ ₚ) (lm : C (₁₊ m)) →
    (x ⁻¹) .proj₁ * b ≡ b₂ →
    ((ract' ᵗ) (inj₂ ((₀ , b) , lm)) (ZM x • ZM y)) ≋
    ((ract' ᵗ) (inj₂ ((₀ , b) , lm)) (ZM (x *' y)))
  Mmul-wd-0 x y b b₂ lm eq₂ = resid≈ , coset≡
    where
    c₂fix : ((ract' ᵗ) (inj₂ ((₀ , b) , lm)) (ZM x)) .proj₂ ≡
            inj₂ ((₀ , b₂) , lm)
    c₂fix = Eq.trans (MD-coset!0 x b lm)
              (Eq.cong (λ v → inj₂ ((₀ , v) , lm)) eq₂)

    y-resid : ((ract' ᵗ) (((ract' ᵗ) (inj₂ ((₀ , b) , lm)) (ZM x)) .proj₂)
                 (ZM y)) .proj₁ ≈ ZM y
    y-resid = trans
      (refl'ᵣ (Eq.cong (λ c → ((ract' ᵗ) c (ZM y)) .proj₁) c₂fix))
      (MD-resid!0 y b₂ lm)

    resid≈ : ((ract' ᵗ) (inj₂ ((₀ , b) , lm)) (ZM x • ZM y)) .proj₁ ≈
             ((ract' ᵗ) (inj₂ ((₀ , b) , lm)) (ZM (x *' y))) .proj₁
    resid≈ = trans (cong (MD-resid!0 x b lm) y-resid)
             (trans (axiom (M-mul x y))
                    (sym (MD-resid!0 (x *' y) b lm)))

    eqf : (y ⁻¹) .proj₁ * b₂ ≡ ((x *' y) ⁻¹) .proj₁ * b
    eqf = Eq.trans (Eq.cong ((y ⁻¹) .proj₁ *_) (Eq.sym eq₂))
          (Eq.trans (Eq.sym (*-assoc ((y ⁻¹) .proj₁) ((x ⁻¹) .proj₁) b))
          (Eq.trans (Eq.cong (_* b) (*-comm ((y ⁻¹) .proj₁) ((x ⁻¹) .proj₁)))
                    (Eq.cong (_* b) (Eq.sym (inv-distrib x y)))))

    coset≡ : ((ract' ᵗ) (inj₂ ((₀ , b) , lm)) (ZM x • ZM y)) .proj₂ ≡
             ((ract' ᵗ) (inj₂ ((₀ , b) , lm)) (ZM (x *' y))) .proj₂
    coset≡ = Eq.trans
      (Eq.cong (λ c → ((ract' ᵗ) c (ZM y)) .proj₂) c₂fix)
      (Eq.trans (MD-coset!0 y b₂ lm)
      (Eq.trans (Eq.cong (λ v → inj₂ ((₀ , v) , lm)) eqf)
                (Eq.sym (MD-coset!0 (x *' y) b lm))))

  Mmul-wd-+ : ∀ (x y : ℤ* ₚ) (a' v' : Fin (₁₊ p-2)) (b b₂ : ℤ ₚ)
    (lm : C (₁₊ m)) →
    x .proj₁ * ₁₊ a' ≡ ₁₊ v' →
    (x ⁻¹) .proj₁ * b ≡ b₂ →
    ((ract' ᵗ) (inj₂ ((₁₊ a' , b) , lm)) (ZM x • ZM y)) ≋
    ((ract' ᵗ) (inj₂ ((₁₊ a' , b) , lm)) (ZM (x *' y)))
  Mmul-wd-+ x y a' v' b b₂ lm eq-v eq₂ = resid≈ , coset≡
    where
    c₂fix : ((ract' ᵗ) (inj₂ ((₁₊ a' , b) , lm)) (ZM x)) .proj₂ ≡
            inj₂ ((₁₊ v' , b₂) , lm)
    c₂fix = Eq.trans (MD-coset!+ x a' b lm)
              (Eq.cong₂ (λ u v → inj₂ ((u , v) , lm)) eq-v eq₂)

    y-resid : ((ract' ᵗ) (((ract' ᵗ) (inj₂ ((₁₊ a' , b) , lm)) (ZM x)) .proj₂)
                 (ZM y)) .proj₁ ≈ ZM (y ⁻¹)
    y-resid = trans
      (refl'ᵣ (Eq.cong (λ c → ((ract' ᵗ) c (ZM y)) .proj₁) c₂fix))
      (MD-resid!+ y v' b₂ lm)

    resid≈ : ((ract' ᵗ) (inj₂ ((₁₊ a' , b) , lm)) (ZM x • ZM y)) .proj₁ ≈
             ((ract' ᵗ) (inj₂ ((₁₊ a' , b) , lm)) (ZM (x *' y))) .proj₁
    resid≈ = trans (cong (MD-resid!+ x a' b lm) y-resid)
             (trans (axiom (M-mul (x ⁻¹) (y ⁻¹)))
             (trans (ZM-val≈ ((x ⁻¹) *' (y ⁻¹)) ((x *' y) ⁻¹)
                      (Eq.sym (inv-distrib x y)))
                    (sym (MD-resid!+ (x *' y) a' b lm))))

    fst-f : y .proj₁ * ₁₊ v' ≡ (x *' y) .proj₁ * ₁₊ a'
    fst-f = Eq.trans (Eq.cong (y .proj₁ *_) (Eq.sym eq-v))
            (Eq.trans (Eq.sym (*-assoc (y .proj₁) (x .proj₁) (₁₊ a')))
                      (Eq.cong (_* ₁₊ a') (*-comm (y .proj₁) (x .proj₁))))

    snd-f : (y ⁻¹) .proj₁ * b₂ ≡ ((x *' y) ⁻¹) .proj₁ * b
    snd-f = Eq.trans (Eq.cong ((y ⁻¹) .proj₁ *_) (Eq.sym eq₂))
            (Eq.trans (Eq.sym (*-assoc ((y ⁻¹) .proj₁) ((x ⁻¹) .proj₁) b))
            (Eq.trans (Eq.cong (_* b) (*-comm ((y ⁻¹) .proj₁) ((x ⁻¹) .proj₁)))
                      (Eq.cong (_* b) (Eq.sym (inv-distrib x y)))))

    coset≡ : ((ract' ᵗ) (inj₂ ((₁₊ a' , b) , lm)) (ZM x • ZM y)) .proj₂ ≡
             ((ract' ᵗ) (inj₂ ((₁₊ a' , b) , lm)) (ZM (x *' y))) .proj₂
    coset≡ = Eq.trans
      (Eq.cong (λ c → ((ract' ᵗ) c (ZM y)) .proj₂) c₂fix)
      (Eq.trans (MD-coset!+ y v' b₂ lm)
      (Eq.trans (Eq.cong₂ (λ u v → inj₂ ((u , v) , lm)) fst-f snd-f)
                (Eq.sym (MD-coset!+ (x *' y) a' b lm))))
