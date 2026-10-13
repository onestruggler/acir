{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0270 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0092 as B92
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0098 as B98
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0260 as B260

p0 : CX02 • CX20 • SWAP02 • X0 • SWAP02 ≈ CX20 • X0 • SWAP02
p0 = by-assoc-and (under (ε) (X0 • SWAP02) B98.proved) Eq.refl Eq.refl

p1 : CX02 • CX20 • SWAP02 • X0 • SWAP02 ≈ CX02 • CX20 • X2
p1 = by-assoc-and (under (CX02 • CX20) (ε) B92.proved) Eq.refl Eq.refl

p2 : CX20 • X0 • SWAP02 ≈ CX02 • CX20 • X2
p2 = trans (sym p0) p1

p3 : CX20 • X0 • SWAP02 ≈ CX20 • X0 • SWAP02
p3 = refl

p4 : CX02 • CX20 • X2 ≈ X0 • CX02 • CX20
p4 = by-assoc-and (under (ε) (ε) B260.proved) Eq.refl Eq.refl

p5 : CX02 • CX20 • X2 ≈ X0 • CX02 • CX20
p5 = trans p4 (refl)

p6 : CX20 • X0 • SWAP02 ≈ X0 • CX02 • CX20
p6 = trans (sym p3) (trans p2 p5)

proved : CX20 • X0 • SWAP02 ≈ X0 • CX02 • CX20
proved = p6
