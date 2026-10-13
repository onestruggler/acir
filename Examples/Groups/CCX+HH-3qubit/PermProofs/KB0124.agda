{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0124 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

import Examples.Groups.CCX+HH-3qubit.Tietze.drel105 as Tdrel105
p0 : X0 • X1 • CX01 ≈ CX01 • X0
p0 = Tdrel105.proved

p1 : X0 • X1 • CX01 ≈ X0 • X1 • CX01
p1 = refl

p2 : CX01 • X0 ≈ CX01 • X0
p2 = refl

p3 : X0 • X1 • CX01 ≈ CX01 • X0
p3 = trans (sym p1) (trans p0 p2)

proved : X0 • X1 • CX01 ≈ CX01 • X0
proved = p3
