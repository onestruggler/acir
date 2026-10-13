{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0086 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0008 as B8
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0084 as B84

p0 : CX02 • CX20 • CX02 • CX02 ≈ SWAP02 • CX02
p0 = by-assoc-and (under (ε) (CX02) B84.proved) Eq.refl Eq.refl

p1 : CX02 • CX20 • CX02 • CX02 ≈ CX02 • CX20
p1 = by-assoc-and (under (CX02 • CX20) (ε) B8.proved) Eq.refl Eq.refl

p2 : SWAP02 • CX02 ≈ CX02 • CX20
p2 = trans (sym p0) p1

p3 : SWAP02 • CX02 ≈ SWAP02 • CX02
p3 = refl

p4 : CX02 • CX20 ≈ CX02 • CX20
p4 = refl

p5 : SWAP02 • CX02 ≈ CX02 • CX20
p5 = trans (sym p3) (trans p2 p4)

proved : SWAP02 • CX02 ≈ CX02 • CX20
proved = p5
