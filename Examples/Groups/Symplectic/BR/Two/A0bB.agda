{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS  --call-by-name #-}
{-# OPTIONS --termination-depth=4 #-}

import Relation.Binary.Reasoning.Setoid as SR



open import Data.Nat hiding (_^_ ; _+_ ; _*_)
--open import Data.List using () hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)


import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Reidemeister-Schreier as RS
open import Notations



open import Data.Nat.Primality



module Examples.Groups.Symplectic.BR.Two.A0bB (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

n : ℕ
n = 0
    




open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)



open import Zp.ModularArithmetic
open import Examples.Groups.Symplectic.Lemmas.Lemmas-2Qupit-Sym p-2 p-prime
open import Examples.Groups.Symplectic.NF2-Sym p-2 p-prime
--open Lemmas-2Q 2

open import Examples.Groups.Symplectic.Lemmas.Ex-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym1 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym2 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3n p-2 p-prime




open PB ((₂₊ n) QRel,_===_)
open PP ((₂₊ n) QRel,_===_)
open SR word-setoid
module L01 = Lemmas0 1

--dir-and-AB' : ℤ* ₚ -> B -> Word (Gen 2) × (A  ⊎ ℤ* ₚ × B)
