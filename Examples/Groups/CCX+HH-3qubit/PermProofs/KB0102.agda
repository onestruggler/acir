{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0102 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0000 as B0
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0100 as B100

p0 : SWAP01 • CX02 • SWAP01 • SWAP01 ≈ CX12 • SWAP01
p0 = by-assoc-and (under (ε) (SWAP01) B100.proved) Eq.refl Eq.refl

p1 : SWAP01 • CX02 • SWAP01 • SWAP01 ≈ SWAP01 • CX02
p1 = by-assoc-and (under (SWAP01 • CX02) (ε) B0.proved) Eq.refl Eq.refl

p2 : CX12 • SWAP01 ≈ SWAP01 • CX02
p2 = trans (sym p0) p1

p3 : CX12 • SWAP01 ≈ CX12 • SWAP01
p3 = refl

p4 : SWAP01 • CX02 ≈ SWAP01 • CX02
p4 = refl

p5 : CX12 • SWAP01 ≈ SWAP01 • CX02
p5 = trans (sym p3) (trans p2 p4)

p6 : SWAP01 • CX02 ≈ CX12 • SWAP01
p6 = sym p5

proved : SWAP01 • CX02 ≈ CX12 • SWAP01
proved = p6
