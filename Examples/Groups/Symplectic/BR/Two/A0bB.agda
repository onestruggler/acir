{-# OPTIONS --cubical-compatible --safe #-}

import Relation.Binary.Reasoning.Setoid as SR



open import Data.Nat hiding (_^_ ; _+_ ; _*_)
--open import Data.List using () hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)


import Presentation.Base as PB
import Presentation.Properties as PP
open import Notations



open import Data.Nat.Primality



module Examples.Groups.Symplectic.BR.Two.A0bB (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

n : ℕ
n = 0
    




open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)



--open Lemmas-2Q 2





open PB ((₂₊ n) QRel,_===_)
open PP ((₂₊ n) QRel,_===_)
open SR word-setoid
module L01 = Lemmas0 1

--dir-and-AB' : ℤ* ₚ -> B -> Word (Gen 2) × (A  ⊎ ℤ* ₚ × B)
