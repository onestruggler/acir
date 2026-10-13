{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0069 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0002 as B2
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0067 as B67

p0 : SWAP02 • CX01 • SWAP02 • SWAP02 ≈ CX21 • SWAP02
p0 = by-assoc-and (under (ε) (SWAP02) B67.proved) Eq.refl Eq.refl

p1 : SWAP02 • CX01 • SWAP02 • SWAP02 ≈ SWAP02 • CX01
p1 = by-assoc-and (under (SWAP02 • CX01) (ε) B2.proved) Eq.refl Eq.refl

p2 : CX21 • SWAP02 ≈ SWAP02 • CX01
p2 = trans (sym p0) p1

p3 : CX21 • SWAP02 ≈ CX21 • SWAP02
p3 = refl

p4 : SWAP02 • CX01 ≈ SWAP02 • CX01
p4 = refl

p5 : CX21 • SWAP02 ≈ SWAP02 • CX01
p5 = trans (sym p3) (trans p2 p4)

p6 : SWAP02 • CX01 ≈ CX21 • SWAP02
p6 = sym p5

proved : SWAP02 • CX01 ≈ CX21 • SWAP02
proved = p6
