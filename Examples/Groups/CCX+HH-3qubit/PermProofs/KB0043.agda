{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0043 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

import Examples.Groups.CCX+HH-3qubit.Tietze.drel183 as Tdrel183
p0 : CX21 • CX20 ≈ CX20 • CX21
p0 = Tdrel183.proved

p1 : CX21 • CX20 ≈ CX21 • CX20
p1 = refl

p2 : CX20 • CX21 ≈ CX20 • CX21
p2 = refl

p3 : CX21 • CX20 ≈ CX20 • CX21
p3 = trans (sym p1) (trans p0 p2)

proved : CX21 • CX20 ≈ CX20 • CX21
proved = p3
