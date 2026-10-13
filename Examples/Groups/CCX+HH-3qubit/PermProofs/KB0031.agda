{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0031 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

import Examples.Groups.CCX+HH-3qubit.Tietze.drel55 as Tdrel55
p0 : CCX01 • CX12 ≈ CX12 • CCX01
p0 = Tdrel55.proved

p1 : CCX01 • CX12 ≈ CCX01 • CX12
p1 = refl

p2 : CX12 • CCX01 ≈ CX12 • CCX01
p2 = refl

p3 : CCX01 • CX12 ≈ CX12 • CCX01
p3 = trans (sym p1) (trans p0 p2)

proved : CCX01 • CX12 ≈ CX12 • CCX01
proved = p3
