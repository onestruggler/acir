{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0111 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0005 as B5
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0042 as B42
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0088 as B88

p0 : CX10 • CX10 • SWAP01 ≈ CX10 • CX01 • CX10
p0 = by-assoc-and (under (CX10) (ε) B42.proved) Eq.refl Eq.refl

p1 : CX10 • CX10 • SWAP01 ≈ SWAP01
p1 = by-assoc-and (under (ε) (SWAP01) B5.proved) Eq.refl Eq.refl

p2 : CX10 • CX01 • CX10 ≈ SWAP01
p2 = trans (sym p0) p1

p3 : CX10 • CX01 • CX10 ≈ CX01 • SWAP01 • CX10
p3 = by-assoc-and (under (ε) (CX10) B88.proved) Eq.refl Eq.refl

p4 : CX10 • CX01 • CX10 ≈ CX01 • SWAP01 • CX10
p4 = trans p3 (refl)

p5 : SWAP01 ≈ SWAP01
p5 = refl

p6 : CX01 • SWAP01 • CX10 ≈ SWAP01
p6 = trans (sym p4) (trans p2 p5)

proved : CX01 • SWAP01 • CX10 ≈ SWAP01
proved = p6
