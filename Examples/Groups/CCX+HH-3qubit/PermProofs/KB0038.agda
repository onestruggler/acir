{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0038 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

import Examples.Groups.CCX+HH-3qubit.Tietze.drel92 as Tdrel92
p0 : CCX02 • CX01 ≈ CX01 • CCX02
p0 = Tdrel92.proved

p1 : CCX02 • CX01 ≈ CCX02 • CX01
p1 = refl

p2 : CX01 • CCX02 ≈ CX01 • CCX02
p2 = refl

p3 : CCX02 • CX01 ≈ CX01 • CCX02
p3 = trans (sym p1) (trans p0 p2)

proved : CCX02 • CX01 ≈ CX01 • CCX02
proved = p3
