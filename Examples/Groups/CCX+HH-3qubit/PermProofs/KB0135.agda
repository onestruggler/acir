{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0135 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0026 as B26

import Examples.Groups.CCX+HH-3qubit.Tietze.drel135 as Tdrel135
p0 : CX12 • CX20 ≈ CX20 • CX12 • CX10
p0 = Tdrel135.proved

p1 : CX12 • CX20 ≈ CX12 • CX20
p1 = refl

p2 : CX20 • CX12 • CX10 ≈ CX20 • CX10 • CX12
p2 = by-assoc-and (under (CX20) (ε) B26.proved) Eq.refl Eq.refl

p3 : CX20 • CX12 • CX10 ≈ CX20 • CX10 • CX12
p3 = trans p2 (refl)

p4 : CX12 • CX20 ≈ CX20 • CX10 • CX12
p4 = trans (sym p1) (trans p0 p3)

p5 : CX20 • CX10 • CX12 ≈ CX12 • CX20
p5 = sym p4

proved : CX20 • CX10 • CX12 ≈ CX12 • CX20
proved = p5
