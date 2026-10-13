{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB4692 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0082 as B82
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1070 as B1070

p0 : CCX02 • CX12 • CCX12 • SWAP12 • CX02 ≈ CX21 • CCX02 • CX12 • CCX12 • CX02
p0 = by-assoc-and (under (ε) (CX02) B1070.proved) Eq.refl Eq.refl

p1 : CCX02 • CX12 • CCX12 • SWAP12 • CX02 ≈ CCX02 • CX12 • CCX12 • CX01 • SWAP12
p1 = by-assoc-and (under (CCX02 • CX12 • CCX12) (ε) B82.proved) Eq.refl Eq.refl

p2 : CX21 • CCX02 • CX12 • CCX12 • CX02 ≈ CCX02 • CX12 • CCX12 • CX01 • SWAP12
p2 = trans (sym p0) p1

p3 : CX21 • CCX02 • CX12 • CCX12 • CX02 ≈ CX21 • CCX02 • CX12 • CCX12 • CX02
p3 = refl

p4 : CCX02 • CX12 • CCX12 • CX01 • SWAP12 ≈ CCX02 • CX12 • CCX12 • CX01 • SWAP12
p4 = refl

p5 : CX21 • CCX02 • CX12 • CCX12 • CX02 ≈ CCX02 • CX12 • CCX12 • CX01 • SWAP12
p5 = trans (sym p3) (trans p2 p4)

p6 : CCX02 • CX12 • CCX12 • CX01 • SWAP12 ≈ CX21 • CCX02 • CX12 • CCX12 • CX02
p6 = sym p5

proved : CCX02 • CX12 • CCX12 • CX01 • SWAP12 ≈ CX21 • CCX02 • CX12 • CCX12 • CX02
proved = p6
