{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0241 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0042 as B42
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0065 as B65

p0 : CX10 • SWAP01 • CX20 ≈ CX10 • CX21 • SWAP01
p0 = by-assoc-and (under (CX10) (ε) B65.proved) Eq.refl Eq.refl

p1 : CX10 • SWAP01 • CX20 ≈ CX01 • CX10 • CX20
p1 = by-assoc-and (under (ε) (CX20) B42.proved) Eq.refl Eq.refl

p2 : CX10 • CX21 • SWAP01 ≈ CX01 • CX10 • CX20
p2 = trans (sym p0) p1

p3 : CX10 • CX21 • SWAP01 ≈ CX10 • CX21 • SWAP01
p3 = refl

p4 : CX01 • CX10 • CX20 ≈ CX01 • CX10 • CX20
p4 = refl

p5 : CX10 • CX21 • SWAP01 ≈ CX01 • CX10 • CX20
p5 = trans (sym p3) (trans p2 p4)

proved : CX10 • CX21 • SWAP01 ≈ CX01 • CX10 • CX20
proved = p5
