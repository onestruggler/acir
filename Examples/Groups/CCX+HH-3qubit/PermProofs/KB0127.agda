{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0127 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

import Examples.Groups.CCX+HH-3qubit.Tietze.drel112 as Tdrel112
p0 : CX01 • CX12 ≈ CX12 • CX01 • CX02
p0 = Tdrel112.proved

p1 : CX01 • CX12 ≈ CX01 • CX12
p1 = refl

p2 : CX12 • CX01 • CX02 ≈ CX12 • CX01 • CX02
p2 = refl

p3 : CX01 • CX12 ≈ CX12 • CX01 • CX02
p3 = trans (sym p1) (trans p0 p2)

p4 : CX12 • CX01 • CX02 ≈ CX01 • CX12
p4 = sym p3

proved : CX12 • CX01 • CX02 ≈ CX01 • CX12
proved = p4
