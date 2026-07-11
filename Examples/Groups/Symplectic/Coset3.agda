{-# OPTIONS  --safe #-}
{-# OPTIONS --termination-depth=2 #-}

open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')


open import Function using (id)
open import Function.Definitions using (Injective)

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



module Examples.Groups.Symplectic.Coset3 (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

open import Examples.Groups.Symplectic.Cosets p-2 p-prime
open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime


data Cosets3 : Set where
  case-I : Cosets2 -> SPowers -> CZPowers -> Cosets3
  case-II : CZPowers -> CZPowers -> Cosets2 -> SPowers -> CZPowers -> Cosets3


