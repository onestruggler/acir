{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS  --call-by-name #-}
{-# OPTIONS --termination-depth=4 #-}

open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq



open import Data.Nat hiding (_^_ ; _+_ ; _*_)
--open import Data.List using () hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Fin hiding (_+_ ; _-_ ; _≤_ ; _<_)


open import Word.Base as WB hiding (wfoldl ; _^'_)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Reidemeister-Schreier as RS
open import Notations



open import Presentation.GroupLike
open import Presentation.Tactic.Rewriting using ()
open import Data.Nat.Primality



module Examples.Groups.Symplectic.BR.One.E (p-2 : ℕ) (p-prime : Prime (2+ p-2)) (n : ℕ)  where

    




open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)
open import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime

open import Examples.Groups.Symplectic.ExtendedGate.Semantics.Properties p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.Soundness p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2)


open import Zp.ModularArithmetic
open import Examples.Groups.Symplectic.NF2-Sym p-2 p-prime
--open Lemmas-2Q 2

open import Examples.Groups.Symplectic.Lemmas.Ex-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym1 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym2 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3 p-2 p-prime
--open import Examples.Groups.Symplectic.Lemmas.Ex-Sym5 p-2 p-prime hiding (module L0)

open Lemmas0a
open Lemmas0a1
open Lemmas0b
open Lemmas0c

--open import Examples.Groups.Symplectic.Lemmas.Coset2-Update-Sym p-2 p-prime renaming (module Completeness to CP2) using ()


open PB ((₁₊ n) QRel,_===_)
open PP ((₁₊ n) QRel,_===_)
open SR word-setoid
open Lemmas0 n

lemma-single-qupit-br-E : ∀ (b : ℤ ₚ) ->

  [ b ]ᵉ • S ≈ [ b + - ₁ ]ᵉ
  
lemma-single-qupit-br-E b = begin
  [ b ]ᵉ • S ≈⟨ refl ⟩
  S^ (- b) • S ≈⟨ lemma-S^k+l (- b) ₁ ⟩
  S^ (- b + ₁) ≡⟨ Eq.cong S^ (Eq.cong (- b +_) (Eq.sym (-‿involutive ₁))) ⟩
  S^ (- b + - - ₁) ≡⟨ Eq.cong S^ (-‿+-comm b (- ₁)) ⟩
  S^ (- (b + - ₁)) ≈⟨ refl ⟩
  [ b + - ₁ ]ᵉ ∎


