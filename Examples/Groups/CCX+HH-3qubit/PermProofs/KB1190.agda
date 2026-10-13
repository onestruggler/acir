{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1190 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0080 as B80
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0295 as B295

p0 : CCX02 • CCX12 • CX21 • CX12 ≈ CX20 • CCX02 • CCX12 • CX12
p0 = by-assoc-and (under (ε) (CX12) B295.proved) Eq.refl Eq.refl

p1 : CCX02 • CCX12 • CX21 • CX12 ≈ CCX02 • CCX12 • CX12 • SWAP12
p1 = by-assoc-and (under (CCX02 • CCX12) (ε) B80.proved) Eq.refl Eq.refl

p2 : CX20 • CCX02 • CCX12 • CX12 ≈ CCX02 • CCX12 • CX12 • SWAP12
p2 = trans (sym p0) p1

p3 : CX20 • CCX02 • CCX12 • CX12 ≈ CX20 • CCX02 • CCX12 • CX12
p3 = refl

p4 : CCX02 • CCX12 • CX12 • SWAP12 ≈ CCX02 • CCX12 • CX12 • SWAP12
p4 = refl

p5 : CX20 • CCX02 • CCX12 • CX12 ≈ CCX02 • CCX12 • CX12 • SWAP12
p5 = trans (sym p3) (trans p2 p4)

p6 : CCX02 • CCX12 • CX12 • SWAP12 ≈ CX20 • CCX02 • CCX12 • CX12
p6 = sym p5

proved : CCX02 • CCX12 • CX12 • SWAP12 ≈ CX20 • CCX02 • CCX12 • CX12
proved = p6
