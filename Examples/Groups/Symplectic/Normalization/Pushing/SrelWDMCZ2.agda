------------------------------------------------------------------------
-- Presentations of groups
--
-- The lifted-word traversal engine: threading w ↑ over an inj₂ coset
-- is threading w over the tail coset with the escapes lifted.  Basis
-- for the semi-M↑CZ inj₂-inj₂ cases.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ2
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (inj₁ ; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

open import Word.Base

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase p-2 p-prime

------------------------------------------------------------------------
-- Threading a lifted word: the top D box is untouched and the escapes
-- are the lifted escapes of the tail threading.

ract-↑-≡ : ∀ {n} (d1 : D) (lm : C (₁₊ n)) (w : Circuit (₁₊ n)) →
  ((ract {₁₊ n} ᵗ) (inj₂ (d1 , lm)) (w ↑)) ≡
  ((((ract {n} ᵗ) lm w) .proj₁) ↑ , inj₂ (d1 , ((ract {n} ᵗ) lm w) .proj₂))
ract-↑-≡ d1 lm [ g ]ʷ = Eq.refl
ract-↑-≡ d1 lm ε = Eq.refl
ract-↑-≡ {n} d1 lm (u • v) =
  Eq.trans
    (Eq.cong (λ pr →
        (pr .proj₁ • ((ract {₁₊ n} ᵗ) (pr .proj₂) (v ↑)) .proj₁ ,
         ((ract {₁₊ n} ᵗ) (pr .proj₂) (v ↑)) .proj₂))
      (ract-↑-≡ d1 lm u))
    (Eq.cong (λ pr →
        ((((ract {n} ᵗ) lm u) .proj₁) ↑ • pr .proj₁ , pr .proj₂))
      (ract-↑-≡ d1 (((ract {n} ᵗ) lm u) .proj₂) v))
