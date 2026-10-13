{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB4626 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0097 as B97
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1048 as B1048

p0 : CX10 • CCX01 • CCX12 • SWAP01 • X0 ≈ CX01 • CX10 • CCX01 • CCX02 • X0
p0 = by-assoc-and (under (ε) (X0) B1048.proved) Eq.refl Eq.refl

p1 : CX10 • CCX01 • CCX12 • SWAP01 • X0 ≈ CX10 • CCX01 • CCX12 • X1 • SWAP01
p1 = by-assoc-and (under (CX10 • CCX01 • CCX12) (ε) B97.proved) Eq.refl Eq.refl

p2 : CX01 • CX10 • CCX01 • CCX02 • X0 ≈ CX10 • CCX01 • CCX12 • X1 • SWAP01
p2 = trans (sym p0) p1

p3 : CX01 • CX10 • CCX01 • CCX02 • X0 ≈ CX01 • CX10 • CCX01 • CCX02 • X0
p3 = refl

p4 : CX10 • CCX01 • CCX12 • X1 • SWAP01 ≈ CX10 • CCX01 • CCX12 • X1 • SWAP01
p4 = refl

p5 : CX01 • CX10 • CCX01 • CCX02 • X0 ≈ CX10 • CCX01 • CCX12 • X1 • SWAP01
p5 = trans (sym p3) (trans p2 p4)

p6 : CX10 • CCX01 • CCX12 • X1 • SWAP01 ≈ CX01 • CX10 • CCX01 • CCX02 • X0
p6 = sym p5

proved : CX10 • CCX01 • CCX12 • X1 • SWAP01 ≈ CX01 • CX10 • CCX01 • CCX02 • X0
proved = p6
