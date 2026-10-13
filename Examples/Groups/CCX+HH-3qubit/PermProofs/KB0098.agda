{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0098 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0086 as B86

p0 : CX20 ≈ SWAP02 • CX02 • SWAP02
p0 = by-assoc-and (axiom r029) Eq.refl Eq.refl

p1 : CX20 ≈ CX20
p1 = refl

p2 : SWAP02 • CX02 • SWAP02 ≈ CX02 • CX20 • SWAP02
p2 = by-assoc-and (under (ε) (SWAP02) B86.proved) Eq.refl Eq.refl

p3 : SWAP02 • CX02 • SWAP02 ≈ CX02 • CX20 • SWAP02
p3 = trans p2 (refl)

p4 : CX20 ≈ CX02 • CX20 • SWAP02
p4 = trans (sym p1) (trans p0 p3)

p5 : CX02 • CX20 • SWAP02 ≈ CX20
p5 = sym p4

proved : CX02 • CX20 • SWAP02 ≈ CX20
proved = p5
