------------------------------------------------------------------------
-- Presentations of groups
--
-- Toward the semi-M↑CZ/M↓CZ width-2 inj₂ coset halves at a (₀,b) A box
-- (the shape-stable branch; a≠0 hits the L'1→L'2 shape-crossing and
-- stays parked).  This file provides the k-fold CZ orbit at an
-- abstract (₀,b) box — OrdCZ-0b's step/orbit generalized from the
-- fixed p-power to any k (its versions are module-private) — the
-- engine both axioms' CZ^ legs run on.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWD2MCZ
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Fin using (Fin ; toℕ)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (inj₂)
open import Data.Vec using ([])
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; _≢_)

open import Word.Base

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime using (C ; ract ; nsum)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushWDM
  p-2 p-prime using (E1 ; GCZd ; inj₂-w1-de-eq)
open import Examples.Groups.Symplectic.Normalization.Pushing.MbSOrder
  p-2 p-prime using (eCZ)

------------------------------------------------------------------------
-- The k-fold CZ orbit at a (₀,b) A box: the L' shape is stable, the D
-- box drifts by nsum t' (−1) in its second slot per step, and the E box
-- absorbs nsum t' (eCZ da) per step (t' = toℕ b⁻¹).

module CZOrbit-0b (b : Fin (₁₊ p-2)) (nz : (₀ , ₁₊ b) ≢ (₀ , ₀)) where

  tCZ : ℕ
  tCZ = toℕ (((₁₊ b , λ ()) ⁻¹) .proj₁)

  cst : D → E → C 2
  cst dd ee = inj₂ (dd , (([] , ee) , ([] , ((₀ , ₁₊ b) , nz))))

  stepCZ : ∀ (da db e : ℤ ₚ) →
    proj₂ (ract {1} (cst (da , db) e) (gate₂ CZ-gate))
    ≡ cst (da , db + nsum tCZ (- ₁)) (e + - nsum tCZ (eCZ da))
  stepCZ da db e =
    inj₂-w1-de-eq (GCZd tCZ da db) (Eq.cong (λ z → e + - z) (E1 tCZ da db))

  orbitCZ : ∀ (k : ℕ) (da db e : ℤ ₚ) →
    ((ract {1} ᵗ) (cst (da , db) e) (CZ ^ k)) .proj₂
    ≡ cst (da , db + nsum k (nsum tCZ (- ₁)))
          (e + nsum k (- nsum tCZ (eCZ da)))
  orbitCZ zero da db e =
    inj₂-w1-de-eq
      (Eq.cong (da ,_) (Eq.sym (+-identityʳ db)))
      (Eq.sym (+-identityʳ e))
  orbitCZ (suc zero) da db e =
    Eq.trans (stepCZ da db e)
      (inj₂-w1-de-eq
        (Eq.cong (da ,_)
          (Eq.cong (db +_) (Eq.sym (+-identityʳ (nsum tCZ (- ₁))))))
        (Eq.cong (e +_) (Eq.sym (+-identityʳ (- nsum tCZ (eCZ da))))))
  orbitCZ (suc (suc k)) da db e =
    Eq.trans (Eq.cong (λ c → ((ract {1} ᵗ) c (CZ ^ suc k)) .proj₂)
        (stepCZ da db e))
    (Eq.trans (orbitCZ (suc k) da (db + nsum tCZ (- ₁))
        (e + - nsum tCZ (eCZ da)))
      (inj₂-w1-de-eq
        (Eq.cong (da ,_)
          (+-assoc db (nsum tCZ (- ₁)) (nsum (suc k) (nsum tCZ (- ₁)))))
        (+-assoc e (- nsum tCZ (eCZ da))
          (nsum (suc k) (- nsum tCZ (eCZ da))))))
