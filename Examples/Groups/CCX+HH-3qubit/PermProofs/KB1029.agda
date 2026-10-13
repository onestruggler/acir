{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1029 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0232 as B232
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0241 as B241

p0 : CX10 • CX21 • SWAP01 • SWAP12 ≈ CX01 • CX10 • CX20 • SWAP12
p0 = by-assoc-and (under (ε) (SWAP12) B241.proved) Eq.refl Eq.refl

p1 : CX10 • CX21 • SWAP01 • SWAP12 ≈ CX10 • CX12 • CX21 • SWAP02
p1 = by-assoc-and (under (CX10) (ε) B232.proved) Eq.refl Eq.refl

p2 : CX01 • CX10 • CX20 • SWAP12 ≈ CX10 • CX12 • CX21 • SWAP02
p2 = trans (sym p0) p1

p3 : CX01 • CX10 • CX20 • SWAP12 ≈ CX01 • CX10 • CX20 • SWAP12
p3 = refl

p4 : CX10 • CX12 • CX21 • SWAP02 ≈ CX10 • CX12 • CX21 • SWAP02
p4 = refl

p5 : CX01 • CX10 • CX20 • SWAP12 ≈ CX10 • CX12 • CX21 • SWAP02
p5 = trans (sym p3) (trans p2 p4)

p6 : CX10 • CX12 • CX21 • SWAP02 ≈ CX01 • CX10 • CX20 • SWAP12
p6 = sym p5

proved : CX10 • CX12 • CX21 • SWAP02 ≈ CX01 • CX10 • CX20 • SWAP12
proved = p6
