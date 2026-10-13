{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0468 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0069 as B69
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0076 as B76
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0086 as B86
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0148 as B148

p0 : SWAP02 • CX02 • CCX02 • CX02 ≈ SWAP02 • CX01 • CCX02
p0 = by-assoc-and (under (SWAP02) (ε) B148.proved) Eq.refl Eq.refl

p1 : SWAP02 • CX02 • CCX02 • CX02 ≈ CX02 • CX20 • CCX02 • CX02
p1 = by-assoc-and (under (ε) (CCX02 • CX02) B86.proved) Eq.refl Eq.refl

p2 : SWAP02 • CX01 • CCX02 ≈ CX02 • CX20 • CCX02 • CX02
p2 = trans (sym p0) p1

p3 : SWAP02 • CX01 • CCX02 ≈ CX21 • SWAP02 • CCX02
p3 = by-assoc-and (under (ε) (CCX02) B69.proved) Eq.refl Eq.refl

p4 : CX21 • SWAP02 • CCX02 ≈ CX21 • CCX02 • SWAP02
p4 = by-assoc-and (under (CX21) (ε) B76.proved) Eq.refl Eq.refl

p5 : SWAP02 • CX01 • CCX02 ≈ CX21 • CCX02 • SWAP02
p5 = trans p3 (trans p4 (refl))

p6 : CX02 • CX20 • CCX02 • CX02 ≈ CX02 • CX20 • CCX02 • CX02
p6 = refl

p7 : CX21 • CCX02 • SWAP02 ≈ CX02 • CX20 • CCX02 • CX02
p7 = trans (sym p5) (trans p2 p6)

p8 : CX02 • CX20 • CCX02 • CX02 ≈ CX21 • CCX02 • SWAP02
p8 = sym p7

proved : CX02 • CX20 • CCX02 • CX02 ≈ CX21 • CCX02 • SWAP02
proved = p8
