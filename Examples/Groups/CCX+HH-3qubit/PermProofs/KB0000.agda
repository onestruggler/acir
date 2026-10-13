{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0000 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as Telim_SWAP01
p0 : SWAP01 • SWAP01 ≈ ε
p0 = Telim_SWAP01.proved

p1 : SWAP01 • SWAP01 ≈ SWAP01 • SWAP01
p1 = refl

p2 : ε ≈ ε
p2 = refl

p3 : SWAP01 • SWAP01 ≈ ε
p3 = trans (sym p1) (trans p0 p2)

proved : SWAP01 • SWAP01 ≈ ε
proved = p3
