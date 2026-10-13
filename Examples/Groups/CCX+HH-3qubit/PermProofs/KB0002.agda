{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0002 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP02 as Telim_SWAP02
p0 : SWAP02 • SWAP02 ≈ ε
p0 = Telim_SWAP02.proved

p1 : SWAP02 • SWAP02 ≈ SWAP02 • SWAP02
p1 = refl

p2 : ε ≈ ε
p2 = refl

p3 : SWAP02 • SWAP02 ≈ ε
p3 = trans (sym p1) (trans p0 p2)

proved : SWAP02 • SWAP02 ≈ ε
proved = p3
