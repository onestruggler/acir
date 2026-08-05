------------------------------------------------------------------------
-- Presentations of groups
--
-- Cascade-vs-collapse, phase 3: the width-2 mb-S cascade in closed
-- form.  With a single (₁₊ α' , β) B box, one cascade step drops the E
-- box by 1, pushes S^ α'² then CZ^ (− α') through the D box (Rof), and
-- leaves the B box fixed: Φ-w2 below.  Leaf file over PushWDM so the
-- edit-check loop stays fast.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.PushWDM2
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (ℕ ; zero ; suc)
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

open import Algebra.Properties.Ring (+-*-ring p-2)
  using (-‿involutive ; -‿+-comm ; -‿distribˡ-* ; -‿distribʳ-*)

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.PushBword
  p-2 p-prime using (No-Top ; sg ; εⁿ ; _•ⁿ_ ; nt-S ; nt-CZ ; nt-^)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushMbS
  p-2 p-prime using (mb-S ; mbSⁿ ; Rof ; Rof-nt)
open import Examples.Groups.Symplectic.Normalization.Pushing.MbSOrder
  p-2 p-prime using (itf ; mbSⁿm ; mbSm ; mbwM ; eCZ ; nsum-* ; mbSⁿ-itf)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDM
  p-2 p-prime using (nsum-neg)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushWD
  p-2 p-prime using (kS0 ; kS0-val ; sqInv ; sqInv-neg ; inj₁-a-eq)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushWDM
  p-2 p-prime using (eCZ-id)

------------------------------------------------------------------------
-- S-power and CZ-power blocks through the one-D-box column.

MBWS : ∀ (t : ℕ) (a b : ℤ ₚ) (ê : E) →
  mbwM (S ^ t) (nt-^ nt-S t) ((a , b) ∷ [] , ê) []
  ≡ ((a , b + nsum t (- a)) ∷ [] , ê)
MBWS zero a b ê =
  Eq.cong (λ z → ((a , z) ∷ [] , ê)) (Eq.sym (+-identityʳ b))
MBWS (suc zero) ₀ ₀ ê =
  Eq.cong₂ _,_
    (Eq.cong (λ z → (₀ , z) ∷ []) (Eq.cong (₀ +_) (Eq.sym (+-identityʳ (- ₀)))))
    (e+-0 ê)
MBWS (suc zero) ₀ (₁₊ b') ê =
  Eq.cong₂ _,_
    (Eq.cong (λ z → (₀ , z) ∷ [])
      (Eq.cong (₁₊ b' +_) (Eq.sym (+-identityʳ (- ₀)))))
    (e+-0 ê)
MBWS (suc zero) (₁₊ i) ₀ ê =
  Eq.cong₂ _,_
    (Eq.cong (λ z → (₁₊ i , z) ∷ [])
      (Eq.cong (₀ +_) (Eq.sym (+-identityʳ (- ₁₊ i)))))
    (e+-0 ê)
MBWS (suc zero) (₁₊ i) (₁₊ b') ê =
  Eq.cong₂ _,_
    (Eq.cong (λ z → (₁₊ i , z) ∷ [])
      (Eq.cong (₁₊ b' +_) (Eq.sym (+-identityʳ (- ₁₊ i)))))
    (e+-0 ê)
MBWS (suc (suc t)) ₀ ₀ ê =
  Eq.trans (Eq.cong
      (λ z → mbwM (S ^ suc t) (nt-^ nt-S (suc t)) ((₀ , ₀ + - ₀) ∷ [] , z) [])
      (e+-0 ê))
  (Eq.trans (MBWS (suc t) ₀ (₀ + - ₀) ê)
    (Eq.cong (λ z → ((₀ , z) ∷ [] , ê))
      (+-assoc ₀ (- ₀) (nsum (suc t) (- ₀)))))
MBWS (suc (suc t)) ₀ (₁₊ b') ê =
  Eq.trans (Eq.cong
      (λ z → mbwM (S ^ suc t) (nt-^ nt-S (suc t)) ((₀ , ₁₊ b' + - ₀) ∷ [] , z) [])
      (e+-0 ê))
  (Eq.trans (MBWS (suc t) ₀ (₁₊ b' + - ₀) ê)
    (Eq.cong (λ z → ((₀ , z) ∷ [] , ê))
      (+-assoc (₁₊ b') (- ₀) (nsum (suc t) (- ₀)))))
MBWS (suc (suc t)) (₁₊ i) ₀ ê =
  Eq.trans (Eq.cong
      (λ z → mbwM (S ^ suc t) (nt-^ nt-S (suc t)) ((₁₊ i , ₀ + - ₁₊ i) ∷ [] , z) [])
      (e+-0 ê))
  (Eq.trans (MBWS (suc t) (₁₊ i) (₀ + - ₁₊ i) ê)
    (Eq.cong (λ z → ((₁₊ i , z) ∷ [] , ê))
      (+-assoc ₀ (- ₁₊ i) (nsum (suc t) (- ₁₊ i)))))
MBWS (suc (suc t)) (₁₊ i) (₁₊ b') ê =
  Eq.trans (Eq.cong
      (λ z → mbwM (S ^ suc t) (nt-^ nt-S (suc t)) ((₁₊ i , ₁₊ b' + - ₁₊ i) ∷ [] , z) [])
      (e+-0 ê))
  (Eq.trans (MBWS (suc t) (₁₊ i) (₁₊ b' + - ₁₊ i) ê)
    (Eq.cong (λ z → ((₁₊ i , z) ∷ [] , ê))
      (+-assoc (₁₊ b') (- ₁₊ i) (nsum (suc t) (- ₁₊ i)))))

MBWCZ : ∀ (t : ℕ) (a b : ℤ ₚ) (ê : E) →
  mbwM (CZ ^ t) (nt-^ nt-CZ t) ((a , b) ∷ [] , ê) []
  ≡ ((a , b + nsum t (- ₁)) ∷ [] , ê + - nsum t (eCZ a))
MBWCZ zero a b ê =
  Eq.cong₂ _,_
    (Eq.cong (λ z → (a , z) ∷ []) (Eq.sym (+-identityʳ b)))
    (Eq.sym (e+-0 ê))
MBWCZ (suc zero) ₀ ₀ ê =
  Eq.cong₂ _,_
    (Eq.cong (λ z → (₀ , z) ∷ [])
      (Eq.cong (₀ +_) (Eq.sym (+-identityʳ (- ₁)))))
    (Eq.cong (λ z → ê + - z) (Eq.sym (+-identityʳ ₀)))
MBWCZ (suc zero) ₀ (₁₊ b') ê =
  Eq.cong₂ _,_
    (Eq.cong (λ z → (₀ , z) ∷ [])
      (Eq.cong (₁₊ b' +_) (Eq.sym (+-identityʳ (- ₁)))))
    (Eq.cong (λ z → ê + - z) (Eq.sym (+-identityʳ ₀)))
MBWCZ (suc zero) (₁₊ i) ₀ ê =
  Eq.cong₂ _,_
    (Eq.cong (λ z → (₁₊ i , z) ∷ [])
      (Eq.cong (₀ +_) (Eq.sym (+-identityʳ (- ₁)))))
    (Eq.cong (λ z → ê + - z) (Eq.sym (+-identityʳ (₁₊ i))))
MBWCZ (suc zero) (₁₊ i) (₁₊ b') ê =
  Eq.cong₂ _,_
    (Eq.cong (λ z → (₁₊ i , z) ∷ [])
      (Eq.cong (₁₊ b' +_) (Eq.sym (+-identityʳ (- ₁)))))
    (Eq.cong (λ z → ê + - z) (Eq.sym (+-identityʳ (₁₊ i))))
MBWCZ (suc (suc t)) ₀ ₀ ê =
  Eq.trans (MBWCZ (suc t) ₀ (₀ + - ₁) (ê + - ₀))
  (Eq.cong₂ _,_
    (Eq.cong (λ z → (₀ , z) ∷ [])
      (+-assoc ₀ (- ₁) (nsum (suc t) (- ₁))))
    (Eq.trans (+-assoc ê (- ₀) (- nsum (suc t) ₀))
      (Eq.cong (ê +_) (-‿+-comm ₀ (nsum (suc t) ₀)))))
MBWCZ (suc (suc t)) ₀ (₁₊ b') ê =
  Eq.trans (MBWCZ (suc t) ₀ (₁₊ b' + - ₁) (ê + - ₀))
  (Eq.cong₂ _,_
    (Eq.cong (λ z → (₀ , z) ∷ [])
      (+-assoc (₁₊ b') (- ₁) (nsum (suc t) (- ₁))))
    (Eq.trans (+-assoc ê (- ₀) (- nsum (suc t) ₀))
      (Eq.cong (ê +_) (-‿+-comm ₀ (nsum (suc t) ₀)))))
MBWCZ (suc (suc t)) (₁₊ i) ₀ ê =
  Eq.trans (MBWCZ (suc t) (₁₊ i) (₀ + - ₁) (ê + - ₁₊ i))
  (Eq.cong₂ _,_
    (Eq.cong (λ z → (₁₊ i , z) ∷ [])
      (+-assoc ₀ (- ₁) (nsum (suc t) (- ₁))))
    (Eq.trans (+-assoc ê (- ₁₊ i) (- nsum (suc t) (₁₊ i)))
      (Eq.cong (ê +_) (-‿+-comm (₁₊ i) (nsum (suc t) (₁₊ i))))))
MBWCZ (suc (suc t)) (₁₊ i) (₁₊ b') ê =
  Eq.trans (MBWCZ (suc t) (₁₊ i) (₁₊ b' + - ₁) (ê + - ₁₊ i))
  (Eq.cong₂ _,_
    (Eq.cong (λ z → (₁₊ i , z) ∷ [])
      (+-assoc (₁₊ b') (- ₁) (nsum (suc t) (- ₁))))
    (Eq.trans (+-assoc ê (- ₁₊ i) (- nsum (suc t) (₁₊ i)))
      (Eq.cong (ê +_) (-‿+-comm (₁₊ i) (nsum (suc t) (₁₊ i))))))

------------------------------------------------------------------------
-- One width-2 cascade step, closed form.

Φ-w2 : ∀ (α' : Fin (₁₊ p-2)) (β : ℤ ₚ) (a b : ℤ ₚ) (ê : E) →
  mbSm ((a , b) ∷ [] , ê) ((₁₊ α' , β) ∷ [])
  ≡ ((a , (b + nsum (toℕ (₁₊ α' * ₁₊ α')) (- a))
            + nsum (toℕ (- ₁₊ α')) (- ₁)) ∷ []
    , (ê + - ₁) + - nsum (toℕ (- ₁₊ α')) (eCZ a))
Φ-w2 α' β a b ê =
  Eq.trans (Eq.cong
      (λ z → mbwM (CZ ^ toℕ (- ₁₊ α')) (nt-^ nt-CZ (toℕ (- ₁₊ α'))) z [])
      (MBWS (toℕ (₁₊ α' * ₁₊ α')) a b (ê + - ₁)))
    (MBWCZ (toℕ (- ₁₊ α')) a (b + nsum (toℕ (₁₊ α' * ₁₊ α')) (- a))
      (ê + - ₁))

------------------------------------------------------------------------
-- Phase 4a: the t-fold cascade in closed form.  The per-step shifts
-- depend only on the (preserved) a-component, so they accumulate as
-- nsum-scaled constants.

Φ-w2-iter : ∀ (t : ℕ) (α' : Fin (₁₊ p-2)) (β : ℤ ₚ) (a b : ℤ ₚ) (ê : E) →
  itf (λ z → mbSm z ((₁₊ α' , β) ∷ [])) t ((a , b) ∷ [] , ê)
  ≡ ((a , b + nsum t (nsum (toℕ (₁₊ α' * ₁₊ α')) (- a)
                      + nsum (toℕ (- ₁₊ α')) (- ₁))) ∷ []
    , ê + nsum t (- ₁ + - nsum (toℕ (- ₁₊ α')) (eCZ a)))
Φ-w2-iter zero α' β a b ê =
  Eq.cong₂ _,_
    (Eq.cong (λ z → (a , z) ∷ []) (Eq.sym (+-identityʳ b)))
    (Eq.sym (+-identityʳ ê))
Φ-w2-iter (suc t) α' β a b ê =
  Eq.trans (Eq.cong (itf (λ z → mbSm z ((₁₊ α' , β) ∷ [])) t)
      (Φ-w2 α' β a b ê))
  (Eq.trans (Φ-w2-iter t α' β a
      ((b + nsum (toℕ (₁₊ α' * ₁₊ α')) (- a)) + nsum (toℕ (- ₁₊ α')) (- ₁))
      ((ê + - ₁) + - nsum (toℕ (- ₁₊ α')) (eCZ a)))
    (Eq.cong₂ _,_
      (Eq.cong (λ z → (a , z) ∷ [])
        (Eq.trans (Eq.cong (_+ nsum t ΔB)
            (+-assoc b (nsum (toℕ (₁₊ α' * ₁₊ α')) (- a))
                       (nsum (toℕ (- ₁₊ α')) (- ₁))))
          (+-assoc b ΔB (nsum t ΔB))))
      (Eq.trans (Eq.cong (_+ nsum t ΔE)
          (+-assoc ê (- ₁) (- nsum (toℕ (- ₁₊ α')) (eCZ a))))
        (+-assoc ê ΔE (nsum t ΔE)))))
  where
  ΔB = nsum (toℕ (₁₊ α' * ₁₊ α')) (- a) + nsum (toℕ (- ₁₊ α')) (- ₁)
  ΔE = - ₁ + - nsum (toℕ (- ₁₊ α')) (eCZ a)

------------------------------------------------------------------------
-- Phase 4b: the value arithmetic.  With α = ₁₊ α', iα = α⁻¹, the
-- collapse maps the box to (da + iα , db) emitting iα·db, and the
-- cascade at weight iα² has per-step shifts ΔB = −α²·(da + iα) + α and
-- ΔE = −1 + α·(da + iα); scaled by iα² these are −da and iα·da — the
-- exact compensations of the pre-collapse d-of-DS route.

module Vals (α' : Fin (₁₊ p-2)) where

  private
    α : ℤ ₚ
    α = ₁₊ α'
    α* : ℤ* ₚ
    α* = (₁₊ α' , λ ())
    iα : ℤ ₚ
    iα = (α* ⁻¹) .proj₁
    instα = nztoℕ {y = α} {neq0 = λ ()}

    ααiα : (α * α) * iα ≡ α
    ααiα = Eq.trans (*-assoc α α iα)
      (Eq.trans (Eq.cong (α *_) (lemma-⁻¹ʳ α {{instα}}))
                (*-identityʳ α))

    IU : (iα * iα) * (α * α) ≡ ₁
    IU = Eq.trans (*-assoc iα iα (α * α))
      (Eq.trans (Eq.cong (iα *_)
          (Eq.trans (Eq.sym (*-assoc iα α α))
            (Eq.trans (Eq.cong (_* α) (lemma-⁻¹ˡ α {{instα}}))
                      (*-identityˡ α))))
        (lemma-⁻¹ˡ α {{instα}}))

  V1 : ∀ (a₀ : ℤ ₚ) →
    nsum (toℕ (α * α)) (- a₀) + nsum (toℕ (- α)) (- ₁)
    ≡ - ((α * α) * a₀) + α
  V1 a₀ = Eq.cong₂ _+_ (nsum-neg (α * α) a₀)
    (Eq.trans (nsum-neg (- α) ₁)
      (Eq.trans (Eq.cong -_ (*-identityʳ (- α))) (-‿involutive α)))

  V2 : ∀ (a₀ : ℤ ₚ) →
    - ₁ + - nsum (toℕ (- α)) (eCZ a₀) ≡ - ₁ + α * a₀
  V2 a₀ = Eq.cong (- ₁ +_)
    (Eq.trans (Eq.cong (λ z → - nsum (toℕ (- α)) z) (eCZ-id a₀))
    (Eq.trans (Eq.cong -_ (nsum-* (- α) a₀))
    (Eq.trans (Eq.cong -_ (Eq.sym (-‿distribˡ-* α a₀)))
              (-‿involutive (α * a₀)))))

  V3 : ∀ (da : ℤ ₚ) →
    - (- da + nsum (toℕ iα) (- ₁)) ≡ da + iα
  V3 da = Eq.trans
    (Eq.cong (λ z → - (- da + z))
      (Eq.trans (nsum-neg iα ₁) (Eq.cong -_ (*-identityʳ iα))))
    (Eq.trans (Eq.cong -_ (-‿+-comm da iα)) (-‿involutive (da + iα)))

  V4 : ∀ (da : ℤ ₚ) →
    (iα * iα) * (- ((α * α) * (da + iα)) + α) ≡ - da
  V4 da =
    Eq.trans (Eq.cong ((iα * iα) *_) d2)
    (Eq.trans (Eq.sym (-‿distribʳ-* (iα * iα) ((α * α) * da)))
              (Eq.cong -_ d4))
    where
    d1 : (α * α) * (da + iα) ≡ ((α * α) * da) + α
    d1 = Eq.trans (*-distribˡ-+ (α * α) da iα)
           (Eq.cong (((α * α) * da) +_) ααiα)
    d2 : - ((α * α) * (da + iα)) + α ≡ - ((α * α) * da)
    d2 = Eq.trans (Eq.cong (λ z → - z + α) d1)
      (Eq.trans (Eq.cong (_+ α) (Eq.sym (-‿+-comm ((α * α) * da) α)))
      (Eq.trans (+-assoc (- ((α * α) * da)) (- α) α)
      (Eq.trans (Eq.cong ((- ((α * α) * da)) +_) (+-inverseˡ α))
                (+-identityʳ (- ((α * α) * da))))))
    d4 : (iα * iα) * ((α * α) * da) ≡ da
    d4 = Eq.trans (Eq.sym (*-assoc (iα * iα) (α * α) da))
           (Eq.trans (Eq.cong (_* da) IU) (*-identityˡ da))

  V5 : ∀ (da : ℤ ₚ) →
    (iα * iα) * (- ₁ + α * (da + iα)) ≡ iα * da
  V5 da =
    Eq.trans (Eq.cong ((iα * iα) *_) e2) e3
    where
    e1 : α * (da + iα) ≡ (α * da) + ₁
    e1 = Eq.trans (*-distribˡ-+ α da iα)
           (Eq.cong ((α * da) +_) (lemma-⁻¹ʳ α {{instα}}))
    e2 : - ₁ + α * (da + iα) ≡ α * da
    e2 = Eq.trans (Eq.cong (- ₁ +_) e1)
      (Eq.trans (Eq.cong (- ₁ +_) (+-comm (α * da) ₁))
      (Eq.trans (Eq.sym (+-assoc (- ₁) ₁ (α * da)))
      (Eq.trans (Eq.cong (_+ (α * da)) (+-inverseˡ ₁))
                (+-0ˡ (α * da)))))
    e3 : (iα * iα) * (α * da) ≡ iα * da
    e3 = Eq.trans (*-assoc iα iα (α * da))
           (Eq.cong (iα *_)
             (Eq.trans (Eq.sym (*-assoc iα α da))
               (Eq.trans (Eq.cong (_* da) (lemma-⁻¹ˡ α {{instα}}))
                         (*-identityˡ da))))

  V6 : ∀ (y : Fin (₁₊ p-2)) (eq-y : - α ≡ ₁₊ y) (X : ℤ ₚ) →
    nsum (toℕ (kS0 {0} y (λ ()))) X ≡ (iα * iα) * X
  V6 y eq-y X = Eq.trans (nsum-* (kS0 {0} y (λ ())) X)
    (Eq.cong (_* X)
      (Eq.trans (kS0-val {0} y (λ ())) (sqInv-neg α' y eq-y)))
