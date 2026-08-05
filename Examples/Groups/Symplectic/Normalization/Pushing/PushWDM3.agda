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
open import Data.Empty using (⊥ ; ⊥-elim)
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
open import Examples.Groups.Symplectic.Normalization.Pushing.PushWDM
  p-2 p-prime using (E1 ; GCZd)
open import Examples.Groups.Symplectic.Normalization.Pushing.MbSOrder
  p-2 p-prime using (eCZ)

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

------------------------------------------------------------------------
-- The (a = 0 , c = 0 , dd = 0) branch: the direction is CZ^ b⁻¹ with
-- the canonical ntH-CZ^ witness, so PushWDM's E1/GCZd closed forms
-- apply on the nose: the D box gains nsum t (− 1) on its b-component
-- and E drops by nsum t (eCZ da) per step, with t = toℕ b⁻¹ fixed.

module OrdCZ-inj₁-00 (b' : Fin (₁₊ p-2)) where

  private
    t : ℕ
    t = toℕ (((₁₊ b' , λ ()) ⁻¹) .proj₁)

  cst : E → D → C 2
  cst e d₀ =
    inj₁ ((d₀ ∷ [] , e) , (((₀ , ₀) ∷ []) , ((₀ , ₁₊ b') , λ ())))

  -- Proof-agnostic collapse onto the canonical coset: the l'-of
  -- no-branch produces a where-lifted nonzero proof, which unifies
  -- away once the value components are rewritten.
  fix : ∀ {d₁ d₂ : D} {e₁ e₂ dd₁ b₁ : ℤ ₚ}
    {pr : _≡_ {A = ℤ ₚ × ℤ ₚ} (₀ , b₁) (₀ , ₀) → ⊥} →
    d₁ ≡ d₂ → e₁ ≡ e₂ → dd₁ ≡ ₀ → b₁ ≡ ₁₊ b' →
    _≡_ {A = C 2}
      (inj₁ ((d₁ ∷ [] , e₁) , (((₀ , dd₁) ∷ []) , ((₀ , b₁) , pr))))
      (cst e₂ d₂)
  fix Eq.refl Eq.refl Eq.refl Eq.refl = Eq.refl

  z00 : ∀ (x : ℤ ₚ) → x + - ₀ ≡ x
  z00 x = Eq.trans (Eq.cong (x +_) -₀≡₀') (+-identityʳ x)
    where
    -₀≡₀' : - ₀ ≡ ₀
    -₀≡₀' = Eq.trans (Eq.sym (+-identityʳ (- z)))
                     (+-inverseˡ z)
      where
      z : ℤ ₚ
      z = ₀

  stepCZ : ∀ (e da db : ℤ ₚ) →
    proj₂ (ract {1} (cst e (da , db)) (gate₂ CZ-gate))
    ≡ cst (e + - nsum t (eCZ da)) (da , db + nsum t (- ₁))
  stepCZ e da db = fix
    (GCZd t da db)
    (Eq.cong (λ z → e + - z) (E1 t da db))
    (z00 ₀)
    (z00 (₁₊ b'))

  cstC : ∀ {e₁ e₂ : ℤ ₚ} {da db₁ db₂ : ℤ ₚ} →
    e₁ ≡ e₂ → db₁ ≡ db₂ → cst e₁ (da , db₁) ≡ cst e₂ (da , db₂)
  cstC {da = da} pe pdb =
    Eq.cong₂ (λ u v → cst u (da , v)) pe pdb

  orbit : ∀ (k : ℕ) (e da db : ℤ ₚ) →
    ((ract {1} ᵗ) (cst e (da , db)) (CZ ^ k)) .proj₂
    ≡ cst (e + nsum k (- nsum t (eCZ da)))
          (da , db + nsum k (nsum t (- ₁)))
  orbit zero e da db =
    cstC (Eq.sym (+-identityʳ e)) (Eq.sym (+-identityʳ db))
  orbit (suc zero) e da db =
    Eq.trans (stepCZ e da db)
      (cstC
        (Eq.cong (e +_) (Eq.sym (+-identityʳ (- nsum t (eCZ da)))))
        (Eq.cong (db +_) (Eq.sym (+-identityʳ (nsum t (- ₁))))))
  orbit (suc (suc k)) e da db =
    Eq.trans (Eq.cong (λ c → ((ract {1} ᵗ) c (CZ ^ suc k)) .proj₂)
        (stepCZ e da db))
    (Eq.trans (orbit (suc k) (e + - nsum t (eCZ da)) da
        (db + nsum t (- ₁)))
      (cstC
        (+-assoc e (- nsum t (eCZ da)) (nsum (suc k) (- nsum t (eCZ da))))
        (+-assoc db (nsum t (- ₁)) (nsum (suc k) (nsum t (- ₁))))))

  ordCZ-inj₁-00-coset : ∀ (e da db : ℤ ₚ) →
    ((ract {1} ᵗ) (cst e (da , db)) (CZ ^ p)) .proj₂
    ≡ ((ract {1} ᵗ) (cst e (da , db)) ε) .proj₂
  ordCZ-inj₁-00-coset e da db =
    Eq.trans (orbit p e da db)
      (cstC
        (Eq.trans (Eq.cong (e +_) (nsum-p≡0 (- nsum t (eCZ da))))
                  (+-identityʳ e))
        (Eq.trans (Eq.cong (db +_) (nsum-p≡0 (nsum t (- ₁))))
                  (+-identityʳ db)))
