{-# OPTIONS --cubical-compatible --safe #-}

import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq

open import Data.Nat hiding (_^_ ; _+_ ; _*_)

open import Word.Base hiding (wfoldl ; _^'_)
import Presentation.Base as PB
import Presentation.Properties as PP
open import Notations

open import Data.Nat.Primality

module Examples.Groups.Symplectic.BR.One.E (p-2 : ℕ) (p-prime : Prime (2+ p-2)) (n : ℕ)  where

open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic hiding (M)
open import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime

open import Algebra.Properties.Ring (+-*-ring p-2)


--open Lemmas-2Q 2



open PB ((₁₊ n) QRel,_===_)
open PP ((₁₊ n) QRel,_===_)
open SR word-setoid
open Lemmas0 n

lemma-single-qupit-br-E : ∀ (b : ℤ ₚ) →

  [ b ]ᵉ • S ≈ [ b + - ₁ ]ᵉ
  
lemma-single-qupit-br-E b = begin
  [ b ]ᵉ • S ≈⟨ refl ⟩
  S^ (- b) • S ≈⟨ lemma-S^k+l (- b) ₁ ⟩
  S^ (- b + ₁) ≡⟨ Eq.cong S^ (Eq.cong (- b +_) (Eq.sym (-‿involutive ₁))) ⟩
  S^ (- b + - - ₁) ≡⟨ Eq.cong S^ (-‿+-comm b (- ₁)) ⟩
  S^ (- (b + - ₁)) ≈⟨ refl ⟩
  [ b + - ₁ ]ᵉ ∎


