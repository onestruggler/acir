{-# OPTIONS  --safe #-}
{-# OPTIONS --termination-depth=2 #-}

open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
open import Relation.Nullary.Decidable using (no)


open import Function using (id)
open import Function.Definitions using (Injective)

open import Data.Product using (_×_)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
open import Agda.Builtin.Nat using (_-_)
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.List hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Vec hiding ([_])
open import Data.Fin hiding (_+_ ; _-_)

open import Data.Maybe

open import Word.Base as WB hiding (wfoldl)
open import Word.Properties
import Normalization.Reidemeister-Schreier as RS
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full

open import Presentation.Construct.Base hiding (_*_ ; _⊕_)


open import Presentation.GroupLike
open import Presentation.Tactic.Rewriting hiding ([_] ; inspect)
open import Data.Nat.Primality



module Examples.Groups.Symplectic.Cosets (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

ZMultiplier = ℤ* ₚ
SPowers = ℤ ₚ

data Cosets1 : Set where
  ε : Cosets1
  HS^ : ℤ ₚ -> Cosets1

data Cosets1-noε : Set where
  HS^ : ℤ ₚ -> Cosets1-noε

MC = ZMultiplier × Cosets1
MC' = ZMultiplier × Cosets1-noε

NF1 = ℤ ₚ × ZMultiplier × Cosets1

CZPowers = ℤ ₚ
CZPowers* = ℤ* ₚ
CZPowers² = CZPowers × CZPowers

Postfix = SPowers × MC × MC

data Cosets2 : Set where
  case-||ₐ : CZPowers -> Postfix -> Cosets2
  case-|| : CZPowers* -> SPowers -> Postfix -> Cosets2
  case-Ex-| : NF1 -> MC -> Cosets2
  case-| : MC -> NF1 -> Cosets2
  case-nf1 : NF1 -> Cosets2
  case-Ex-nf1 : NF1 -> Cosets2

