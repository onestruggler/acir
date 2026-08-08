{-# OPTIONS --cubical-compatible --safe #-}




open import Data.Product using (_×_)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)


import Normalization.Reidemeister-Schreier as RS
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full



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

