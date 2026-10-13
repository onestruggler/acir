{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0316 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0093 as B93
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0098 as B98
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0160 as B160
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0270 as B270

p0 : CX02 • CX20 • SWAP02 • X2 ≈ CX20 • X2
p0 = by-assoc-and (under (ε) (X2) B98.proved) Eq.refl Eq.refl

p1 : CX02 • CX20 • SWAP02 • X2 ≈ CX02 • CX20 • X0 • SWAP02
p1 = by-assoc-and (under (CX02 • CX20) (ε) B93.proved) Eq.refl Eq.refl

p2 : CX20 • X2 ≈ CX02 • CX20 • X0 • SWAP02
p2 = trans (sym p0) p1

p3 : CX20 • X2 ≈ CX20 • X2
p3 = refl

p4 : CX02 • CX20 • X0 • SWAP02 ≈ CX02 • X0 • CX02 • CX20
p4 = by-assoc-and (under (CX02) (ε) B270.proved) Eq.refl Eq.refl

p5 : CX02 • X0 • CX02 • CX20 ≈ X0 • X2 • CX20
p5 = by-assoc-and (under (ε) (CX20) B160.proved) Eq.refl Eq.refl

p6 : CX02 • CX20 • X0 • SWAP02 ≈ X0 • X2 • CX20
p6 = trans p4 (trans p5 (refl))

p7 : CX20 • X2 ≈ X0 • X2 • CX20
p7 = trans (sym p3) (trans p2 p6)

p8 : X0 • X2 • CX20 ≈ CX20 • X2
p8 = sym p7

proved : X0 • X2 • CX20 ≈ CX20 • X2
proved = p8
