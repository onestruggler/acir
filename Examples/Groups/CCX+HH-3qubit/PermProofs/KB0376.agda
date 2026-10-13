{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0376 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0088 as B88
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0090 as B90
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0102 as B102
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0119 as B119

p0 : CX10 • CX01 • CCX02 • CX02 ≈ CX10 • CX02 • CCX02
p0 = by-assoc-and (under (CX10) (ε) B119.proved) Eq.refl Eq.refl

p1 : CX10 • CX01 • CCX02 • CX02 ≈ CX01 • SWAP01 • CCX02 • CX02
p1 = by-assoc-and (under (ε) (CCX02 • CX02) B88.proved) Eq.refl Eq.refl

p2 : CX10 • CX02 • CCX02 ≈ CX01 • SWAP01 • CCX02 • CX02
p2 = trans (sym p0) p1

p3 : CX10 • CX02 • CCX02 ≈ CX10 • CX02 • CCX02
p3 = refl

p4 : CX01 • SWAP01 • CCX02 • CX02 ≈ CX01 • CCX12 • SWAP01 • CX02
p4 = by-assoc-and (under (CX01) (CX02) B90.proved) Eq.refl Eq.refl

p5 : CX01 • CCX12 • SWAP01 • CX02 ≈ CX01 • CCX12 • CX12 • SWAP01
p5 = by-assoc-and (under (CX01 • CCX12) (ε) B102.proved) Eq.refl Eq.refl

p6 : CX01 • SWAP01 • CCX02 • CX02 ≈ CX01 • CCX12 • CX12 • SWAP01
p6 = trans p4 (trans p5 (refl))

p7 : CX10 • CX02 • CCX02 ≈ CX01 • CCX12 • CX12 • SWAP01
p7 = trans (sym p3) (trans p2 p6)

p8 : CX01 • CCX12 • CX12 • SWAP01 ≈ CX10 • CX02 • CCX02
p8 = sym p7

proved : CX01 • CCX12 • CX12 • SWAP01 ≈ CX10 • CX02 • CCX02
proved = p8
