{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0117 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

import Examples.Groups.CCX+HH-3qubit.Tietze.drel70 as Tdrel70
p0 : CX12 • X1 ≈ X1 • X2 • CX12
p0 = Tdrel70.proved

p1 : CX12 • X1 ≈ CX12 • X1
p1 = refl

p2 : X1 • X2 • CX12 ≈ X1 • X2 • CX12
p2 = refl

p3 : CX12 • X1 ≈ X1 • X2 • CX12
p3 = trans (sym p1) (trans p0 p2)

p4 : X1 • X2 • CX12 ≈ CX12 • X1
p4 = sym p3

proved : X1 • X2 • CX12 ≈ CX12 • X1
proved = p4
