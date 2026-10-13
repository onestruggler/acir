{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0009 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX20 as Telim_CX20
p0 : CX20 • CX20 ≈ ε
p0 = Telim_CX20.proved

p1 : CX20 • CX20 ≈ CX20 • CX20
p1 = refl

p2 : ε ≈ ε
p2 = refl

p3 : CX20 • CX20 ≈ ε
p3 = trans (sym p1) (trans p0 p2)

proved : CX20 • CX20 ≈ ε
proved = p3
