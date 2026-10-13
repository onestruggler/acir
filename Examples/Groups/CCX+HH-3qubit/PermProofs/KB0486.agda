{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0486 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0021 as B21
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0088 as B88
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0090 as B90
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0154 as B154

p0 : CX10 • X2 • CCX02 • X2 ≈ CX10 • CX01 • CCX02
p0 = by-assoc-and (under (CX10) (ε) B154.proved) Eq.refl Eq.refl

p1 : CX10 • X2 • CCX02 • X2 ≈ X2 • CX10 • CCX02 • X2
p1 = by-assoc-and (under (ε) (CCX02 • X2) B21.proved) Eq.refl Eq.refl

p2 : CX10 • CX01 • CCX02 ≈ X2 • CX10 • CCX02 • X2
p2 = trans (sym p0) p1

p3 : CX10 • CX01 • CCX02 ≈ CX01 • SWAP01 • CCX02
p3 = by-assoc-and (under (ε) (CCX02) B88.proved) Eq.refl Eq.refl

p4 : CX01 • SWAP01 • CCX02 ≈ CX01 • CCX12 • SWAP01
p4 = by-assoc-and (under (CX01) (ε) B90.proved) Eq.refl Eq.refl

p5 : CX10 • CX01 • CCX02 ≈ CX01 • CCX12 • SWAP01
p5 = trans p3 (trans p4 (refl))

p6 : X2 • CX10 • CCX02 • X2 ≈ X2 • CX10 • CCX02 • X2
p6 = refl

p7 : CX01 • CCX12 • SWAP01 ≈ X2 • CX10 • CCX02 • X2
p7 = trans (sym p5) (trans p2 p6)

p8 : X2 • CX10 • CCX02 • X2 ≈ CX01 • CCX12 • SWAP01
p8 = sym p7

proved : X2 • CX10 • CCX02 • X2 ≈ CX01 • CCX12 • SWAP01
proved = p8
