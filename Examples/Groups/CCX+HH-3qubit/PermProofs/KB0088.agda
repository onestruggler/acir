{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0088 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0013 as B13
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0087 as B87

p0 : CX01 • CX01 • CX10 • CX01 ≈ CX01 • SWAP01
p0 = by-assoc-and (under (CX01) (ε) B87.proved) Eq.refl Eq.refl

p1 : CX01 • CX01 • CX10 • CX01 ≈ CX10 • CX01
p1 = by-assoc-and (under (ε) (CX10 • CX01) B13.proved) Eq.refl Eq.refl

p2 : CX01 • SWAP01 ≈ CX10 • CX01
p2 = trans (sym p0) p1

p3 : CX01 • SWAP01 ≈ CX01 • SWAP01
p3 = refl

p4 : CX10 • CX01 ≈ CX10 • CX01
p4 = refl

p5 : CX01 • SWAP01 ≈ CX10 • CX01
p5 = trans (sym p3) (trans p2 p4)

p6 : CX10 • CX01 ≈ CX01 • SWAP01
p6 = sym p5

proved : CX10 • CX01 ≈ CX01 • SWAP01
proved = p6
