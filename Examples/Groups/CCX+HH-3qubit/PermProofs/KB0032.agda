{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0032 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

import Examples.Groups.CCX+HH-3qubit.Tietze.drel56 as Tdrel56
p0 : CCX12 • CX10 ≈ CX10 • CCX12
p0 = Tdrel56.proved

p1 : CCX12 • CX10 ≈ CCX12 • CX10
p1 = refl

p2 : CX10 • CCX12 ≈ CX10 • CCX12
p2 = refl

p3 : CCX12 • CX10 ≈ CX10 • CCX12
p3 = trans (sym p1) (trans p0 p2)

proved : CCX12 • CX10 ≈ CX10 • CCX12
proved = p3
