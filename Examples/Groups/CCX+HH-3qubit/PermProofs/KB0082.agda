{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0082 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0001 as B1
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0081 as B81

p0 : SWAP12 • SWAP12 • CX01 • SWAP12 ≈ SWAP12 • CX02
p0 = by-assoc-and (under (SWAP12) (ε) B81.proved) Eq.refl Eq.refl

p1 : SWAP12 • SWAP12 • CX01 • SWAP12 ≈ CX01 • SWAP12
p1 = by-assoc-and (under (ε) (CX01 • SWAP12) B1.proved) Eq.refl Eq.refl

p2 : SWAP12 • CX02 ≈ CX01 • SWAP12
p2 = trans (sym p0) p1

p3 : SWAP12 • CX02 ≈ SWAP12 • CX02
p3 = refl

p4 : CX01 • SWAP12 ≈ CX01 • SWAP12
p4 = refl

p5 : SWAP12 • CX02 ≈ CX01 • SWAP12
p5 = trans (sym p3) (trans p2 p4)

proved : SWAP12 • CX02 ≈ CX01 • SWAP12
proved = p5
