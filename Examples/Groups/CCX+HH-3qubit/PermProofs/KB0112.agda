{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0112 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0005 as B5
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0111 as B111

p0 : CX01 • SWAP01 • CX10 • CX10 ≈ SWAP01 • CX10
p0 = by-assoc-and (under (ε) (CX10) B111.proved) Eq.refl Eq.refl

p1 : CX01 • SWAP01 • CX10 • CX10 ≈ CX01 • SWAP01
p1 = by-assoc-and (under (CX01 • SWAP01) (ε) B5.proved) Eq.refl Eq.refl

p2 : SWAP01 • CX10 ≈ CX01 • SWAP01
p2 = trans (sym p0) p1

p3 : SWAP01 • CX10 ≈ SWAP01 • CX10
p3 = refl

p4 : CX01 • SWAP01 ≈ CX01 • SWAP01
p4 = refl

p5 : SWAP01 • CX10 ≈ CX01 • SWAP01
p5 = trans (sym p3) (trans p2 p4)

proved : SWAP01 • CX10 ≈ CX01 • SWAP01
proved = p5
