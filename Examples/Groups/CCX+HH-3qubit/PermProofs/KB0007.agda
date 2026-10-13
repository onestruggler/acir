{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0007 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX21 as Telim_CX21
p0 : CX21 • CX21 ≈ ε
p0 = Telim_CX21.proved

p1 : CX21 • CX21 ≈ CX21 • CX21
p1 = refl

p2 : ε ≈ ε
p2 = refl

p3 : CX21 • CX21 ≈ ε
p3 = trans (sym p1) (trans p0 p2)

proved : CX21 • CX21 ≈ ε
proved = p3
