{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1100 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0090 as B90
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0261 as B261

p0 : CX12 • CX01 • SWAP01 • CCX02 ≈ CX10 • CX12 • CX01 • CCX02
p0 = by-assoc-and (under (ε) (CCX02) B261.proved) Eq.refl Eq.refl

p1 : CX12 • CX01 • SWAP01 • CCX02 ≈ CX12 • CX01 • CCX12 • SWAP01
p1 = by-assoc-and (under (CX12 • CX01) (ε) B90.proved) Eq.refl Eq.refl

p2 : CX10 • CX12 • CX01 • CCX02 ≈ CX12 • CX01 • CCX12 • SWAP01
p2 = trans (sym p0) p1

p3 : CX10 • CX12 • CX01 • CCX02 ≈ CX10 • CX12 • CX01 • CCX02
p3 = refl

p4 : CX12 • CX01 • CCX12 • SWAP01 ≈ CX12 • CX01 • CCX12 • SWAP01
p4 = refl

p5 : CX10 • CX12 • CX01 • CCX02 ≈ CX12 • CX01 • CCX12 • SWAP01
p5 = trans (sym p3) (trans p2 p4)

p6 : CX12 • CX01 • CCX12 • SWAP01 ≈ CX10 • CX12 • CX01 • CCX02
p6 = sym p5

proved : CX12 • CX01 • CCX12 • SWAP01 ≈ CX10 • CX12 • CX01 • CCX02
proved = p6
