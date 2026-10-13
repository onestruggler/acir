{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0259 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0025 as B25
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0069 as B69
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0086 as B86

p0 : SWAP02 • CX02 • CX01 ≈ CX02 • CX20 • CX01
p0 = by-assoc-and (under (ε) (CX01) B86.proved) Eq.refl Eq.refl

p1 : SWAP02 • CX02 • CX01 ≈ SWAP02 • CX01 • CX02
p1 = by-assoc-and (under (SWAP02) (ε) B25.proved) Eq.refl Eq.refl

p2 : CX02 • CX20 • CX01 ≈ SWAP02 • CX01 • CX02
p2 = trans (sym p0) p1

p3 : CX02 • CX20 • CX01 ≈ CX02 • CX20 • CX01
p3 = refl

p4 : SWAP02 • CX01 • CX02 ≈ CX21 • SWAP02 • CX02
p4 = by-assoc-and (under (ε) (CX02) B69.proved) Eq.refl Eq.refl

p5 : CX21 • SWAP02 • CX02 ≈ CX21 • CX02 • CX20
p5 = by-assoc-and (under (CX21) (ε) B86.proved) Eq.refl Eq.refl

p6 : SWAP02 • CX01 • CX02 ≈ CX21 • CX02 • CX20
p6 = trans p4 (trans p5 (refl))

p7 : CX02 • CX20 • CX01 ≈ CX21 • CX02 • CX20
p7 = trans (sym p3) (trans p2 p6)

p8 : CX21 • CX02 • CX20 ≈ CX02 • CX20 • CX01
p8 = sym p7

proved : CX21 • CX02 • CX20 ≈ CX02 • CX20 • CX01
proved = p8
