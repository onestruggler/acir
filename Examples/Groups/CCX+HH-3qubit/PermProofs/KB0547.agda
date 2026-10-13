{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0547 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0040 as B40
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0138 as B138
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0176 as B176

p0 : CCX12 • CX20 • CX21 • CCX02 ≈ CCX12 • CCX02 • CX20
p0 = by-assoc-and (under (CCX12) (ε) B176.proved) Eq.refl Eq.refl

p1 : CCX12 • CX20 • CX21 • CCX02 ≈ CX20 • CCX12 • CX21 • CCX02
p1 = by-assoc-and (under (ε) (CX21 • CCX02) B40.proved) Eq.refl Eq.refl

p2 : CCX12 • CCX02 • CX20 ≈ CX20 • CCX12 • CX21 • CCX02
p2 = trans (sym p0) p1

p3 : CCX12 • CCX02 • CX20 ≈ CCX12 • CCX02 • CX20
p3 = refl

p4 : CX20 • CCX12 • CX21 • CCX02 ≈ CX21 • CCX12 • CCX02
p4 = by-assoc-and (under (ε) (CCX02) B138.proved) Eq.refl Eq.refl

p5 : CX20 • CCX12 • CX21 • CCX02 ≈ CX21 • CCX12 • CCX02
p5 = trans p4 (refl)

p6 : CCX12 • CCX02 • CX20 ≈ CX21 • CCX12 • CCX02
p6 = trans (sym p3) (trans p2 p5)

proved : CCX12 • CCX02 • CX20 ≈ CX21 • CCX12 • CCX02
proved = p6
