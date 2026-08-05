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
  using (-‿involutive ; -‿+-comm)

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.PushBword
  p-2 p-prime using (No-Top ; sg ; εⁿ ; _•ⁿ_ ; nt-S ; nt-CZ ; nt-^)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushMbS
  p-2 p-prime using (mb-S ; mbSⁿ ; Rof ; Rof-nt)
open import Examples.Groups.Symplectic.Normalization.Pushing.MbSOrder
  p-2 p-prime using (itf ; mbSⁿm ; mbSm ; mbwM ; eCZ)
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
