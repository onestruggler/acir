{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0034 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

import Examples.Groups.CCX+HH-3qubit.Tietze.drel79 as Tdrel79
p0 : X1 • CX21 ≈ CX21 • X1
p0 = Tdrel79.proved

p1 : X1 • CX21 ≈ X1 • CX21
p1 = refl

p2 : CX21 • X1 ≈ CX21 • X1
p2 = refl

p3 : X1 • CX21 ≈ CX21 • X1
p3 = trans (sym p1) (trans p0 p2)

p4 : CX21 • X1 ≈ X1 • CX21
p4 = sym p3

proved : CX21 • X1 ≈ X1 • CX21
proved = p4
