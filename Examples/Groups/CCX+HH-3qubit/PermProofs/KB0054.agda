{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0054 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_X_c as Tsymmetry_X_c
p0 : X2 ≈ SWAP12 • X1 • SWAP12
p0 = Tsymmetry_X_c.proved

p1 : X2 ≈ X2
p1 = refl

p2 : SWAP12 • X1 • SWAP12 ≈ SWAP12 • X1 • SWAP12
p2 = refl

p3 : X2 ≈ SWAP12 • X1 • SWAP12
p3 = trans (sym p1) (trans p0 p2)

p4 : SWAP12 • X1 • SWAP12 ≈ X2
p4 = sym p3

proved : SWAP12 • X1 • SWAP12 ≈ X2
proved = p4
