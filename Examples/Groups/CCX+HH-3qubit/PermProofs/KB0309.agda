{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0309 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0001 as B1
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0015 as B15
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0070 as B70
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0072 as B72
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0247 as B247

p0 : SWAP12 • CX10 • SWAP12 • X0 ≈ CX20 • X0
p0 = by-assoc-and (under (ε) (X0) B70.proved) Eq.refl Eq.refl

p1 : SWAP12 • CX10 • SWAP12 • X0 ≈ SWAP12 • CX10 • X0 • SWAP12
p1 = by-assoc-and (under (SWAP12 • CX10) (ε) B15.proved) Eq.refl Eq.refl

p2 : CX20 • X0 ≈ SWAP12 • CX10 • X0 • SWAP12
p2 = trans (sym p0) p1

p3 : CX20 • X0 ≈ CX20 • X0
p3 = refl

p4 : SWAP12 • CX10 • X0 • SWAP12 ≈ CX20 • SWAP12 • X0 • SWAP12
p4 = by-assoc-and (under (ε) (X0 • SWAP12) B72.proved) Eq.refl Eq.refl

p5 : CX20 • SWAP12 • X0 • SWAP12 ≈ CX20 • X0 • SWAP12 • SWAP12
p5 = by-assoc-and (under (CX20) (SWAP12) B15.proved) Eq.refl Eq.refl

p6 : CX20 • X0 • SWAP12 • SWAP12 ≈ X0 • CX20 • SWAP12 • SWAP12
p6 = by-assoc-and (under (ε) (SWAP12) B247.proved) Eq.refl Eq.refl

p7 : X0 • CX20 • SWAP12 • SWAP12 ≈ X0 • CX20
p7 = by-assoc-and (under (X0 • CX20) (ε) B1.proved) Eq.refl Eq.refl

p8 : SWAP12 • CX10 • X0 • SWAP12 ≈ X0 • CX20
p8 = trans p4 (trans p5 (trans p6 (trans p7 (refl))))

p9 : CX20 • X0 ≈ X0 • CX20
p9 = trans (sym p3) (trans p2 p8)

proved : CX20 • X0 ≈ X0 • CX20
proved = p9
