{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0070 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_j as Tsymmetry_CX_j
p0 : CX20 ≈ SWAP12 • CX10 • SWAP12
p0 = Tsymmetry_CX_j.proved

p1 : CX20 ≈ CX20
p1 = refl

p2 : SWAP12 • CX10 • SWAP12 ≈ SWAP12 • CX10 • SWAP12
p2 = refl

p3 : CX20 ≈ SWAP12 • CX10 • SWAP12
p3 = trans (sym p1) (trans p0 p2)

p4 : SWAP12 • CX10 • SWAP12 ≈ CX20
p4 = sym p3

proved : SWAP12 • CX10 • SWAP12 ≈ CX20
proved = p4
