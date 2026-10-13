{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0397 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0074 as B74
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0087 as B87
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0102 as B102
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0123 as B123

p0 : CX01 • CX10 • CX01 • CX02 • CCX01 ≈ CX01 • CX10 • CCX01 • CX01
p0 = by-assoc-and (under (CX01 • CX10) (ε) B123.proved) Eq.refl Eq.refl

p1 : CX01 • CX10 • CX01 • CX02 • CCX01 ≈ SWAP01 • CX02 • CCX01
p1 = by-assoc-and (under (ε) (CX02 • CCX01) B87.proved) Eq.refl Eq.refl

p2 : CX01 • CX10 • CCX01 • CX01 ≈ SWAP01 • CX02 • CCX01
p2 = trans (sym p0) p1

p3 : CX01 • CX10 • CCX01 • CX01 ≈ CX01 • CX10 • CCX01 • CX01
p3 = refl

p4 : SWAP01 • CX02 • CCX01 ≈ CX12 • SWAP01 • CCX01
p4 = by-assoc-and (under (ε) (CCX01) B102.proved) Eq.refl Eq.refl

p5 : CX12 • SWAP01 • CCX01 ≈ CX12 • CCX01 • SWAP01
p5 = by-assoc-and (under (CX12) (ε) B74.proved) Eq.refl Eq.refl

p6 : SWAP01 • CX02 • CCX01 ≈ CX12 • CCX01 • SWAP01
p6 = trans p4 (trans p5 (refl))

p7 : CX01 • CX10 • CCX01 • CX01 ≈ CX12 • CCX01 • SWAP01
p7 = trans (sym p3) (trans p2 p6)

proved : CX01 • CX10 • CCX01 • CX01 ≈ CX12 • CCX01 • SWAP01
proved = p7
