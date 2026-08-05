------------------------------------------------------------------------
-- Presentations of groups
--
-- order-CZ width-2 COSET halves on inj₁ cosets, the drift branches.
-- With an a-nonzero A box the LCZ2 collapse takes the no-test clause
-- every step: for a (₀ , dd) B box the CZ direction is ε and only the
-- B box's d-component drifts (by − a per step); the p-orbit closes by
-- nsum-p≡0.  Leaf file over the cached interfaces so the edit-check
-- loop stays fast.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.PushWDM3
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ)
open import Data.Vec using (Vec ; [] ; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; _≢_)

open import Word.Base

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime
open import Examples.Groups.Symplectic.BR.Two.D-w p-2 p-prime as TDw
  using (push-D-w)
open import Examples.Groups.Symplectic.Normalization.Pushing.Push2
  p-2 p-prime using (coset)

------------------------------------------------------------------------
-- The (a ≠ 0 , c = 0) branch: direction ε, pure d-drift.

module OrdCZ-inj₁-c0 (a' : Fin (₁₊ p-2)) where

  -- A-box equality with the pinned absurd proof.
  A-fix : ∀ {b₁ b₂ : ℤ ₚ} → b₁ ≡ b₂ →
    _≡_ {A = A} ((₁₊ a' , b₁) , λ ()) ((₁₊ a' , b₂) , λ ())
  A-fix Eq.refl = Eq.refl

  cst : ℤ ₚ → ℤ ₚ → E → D → C 2
  cst dd b e d₀ =
    inj₁ ((d₀ ∷ [] , e) , (((₀ , dd) ∷ []) , ((₁₊ a' , b) , λ ())))

  cst-cong : ∀ {dd₁ dd₂ b₁ b₂ e₁ e₂ : ℤ ₚ} {d₀ : D} →
    dd₁ ≡ dd₂ → b₁ ≡ b₂ → e₁ ≡ e₂ →
    cst dd₁ b₁ e₁ d₀ ≡ cst dd₂ b₂ e₂ d₀
  cst-cong {d₀ = d₀} pdd pb pe =
    Eq.cong₂ (λ u v → inj₁ ((d₀ ∷ [] , u) , v)) pe
      (Eq.cong₂ (λ u v → ((₀ , u) ∷ []) , v) pdd (A-fix pb))

  -- One CZ step: the collapse direction is ε (a ≠ 0 with a zero-a B
  -- box), the D box and E pick up only removable ₀-junk, and the B
  -- box's d-component drops by a.  The dd-split lets the LCZ2 case
  -- tree (which examines the B box's d-component first) reduce.
  stepCZ : ∀ (d₀ : D) (e dd b : ℤ ₚ) →
    proj₂ (ract {1} (cst dd b e d₀) (gate₂ CZ-gate))
    ≡ cst (dd + - ₁₊ a') (b + - ₀) (e + - ₀) d₀
  stepCZ d₀ e ₀ b = Eq.refl
  stepCZ d₀ e (₁₊ dd') b = Eq.refl

  orbit : ∀ (k : ℕ) (d₀ : D) (e dd b : ℤ ₚ) →
    ((ract {1} ᵗ) (cst dd b e d₀) (CZ ^ k)) .proj₂
    ≡ cst (dd + nsum k (- ₁₊ a')) (b + nsum k (- ₀)) (e + nsum k (- ₀)) d₀
  orbit zero d₀ e dd b =
    cst-cong (Eq.sym (+-identityʳ dd)) (Eq.sym (+-identityʳ b))
             (Eq.sym (+-identityʳ e))
  orbit (suc zero) d₀ e dd b =
    Eq.trans (stepCZ d₀ e dd b)
      (cst-cong
        (Eq.cong (dd +_) (Eq.sym (+-identityʳ (- ₁₊ a'))))
        (Eq.cong (b +_) (Eq.sym (+-identityʳ (- ₀))))
        (Eq.cong (e +_) (Eq.sym (+-identityʳ (- ₀)))))
  orbit (suc (suc k)) d₀ e dd b =
    Eq.trans (Eq.cong (λ c → ((ract {1} ᵗ) c (CZ ^ suc k)) .proj₂)
        (stepCZ d₀ e dd b))
    (Eq.trans (orbit (suc k) d₀ (e + - ₀) (dd + - ₁₊ a') (b + - ₀))
      (cst-cong
        (+-assoc dd (- ₁₊ a') (nsum (suc k) (- ₁₊ a')))
        (+-assoc b (- ₀) (nsum (suc k) (- ₀)))
        (+-assoc e (- ₀) (nsum (suc k) (- ₀)))))

  ordCZ-inj₁-c0-coset : ∀ (d₀ : D) (e dd b : ℤ ₚ) →
    ((ract {1} ᵗ) (cst dd b e d₀) (CZ ^ p)) .proj₂
    ≡ ((ract {1} ᵗ) (cst dd b e d₀) ε) .proj₂
  ordCZ-inj₁-c0-coset d₀ e dd b =
    Eq.trans (orbit p d₀ e dd b)
      (cst-cong
        (Eq.trans (Eq.cong (dd +_) (nsum-p≡0 (- ₁₊ a'))) (+-identityʳ dd))
        (Eq.trans (Eq.cong (b +_) (nsum-p≡0 (- ₀))) (+-identityʳ b))
        (Eq.trans (Eq.cong (e +_) (nsum-p≡0 (- ₀))) (+-identityʳ e)))
