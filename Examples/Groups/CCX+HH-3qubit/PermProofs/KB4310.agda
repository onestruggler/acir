{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB4310 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0315 as B315
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0811 as B811
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB3908 as B3908

p0 : CX10 • CX02 • CCX12 • CCX01 • SWAP02 ≈ CX10 • X1 • CCX12 • CCX01 • X1
p0 = by-assoc-and (under (CX10) (ε) B811.proved) Eq.refl Eq.refl

p1 : CX10 • CX02 • CCX12 • CCX01 • SWAP02 ≈ CX02 • CCX12 • CX12 • CCX01 • SWAP02
p1 = by-assoc-and (under (ε) (CCX01 • SWAP02) B315.proved) Eq.refl Eq.refl

p2 : CX10 • X1 • CCX12 • CCX01 • X1 ≈ CX02 • CCX12 • CX12 • CCX01 • SWAP02
p2 = trans (sym p0) p1

p3 : CX10 • X1 • CCX12 • CCX01 • X1 ≈ CX10 • X1 • CCX12 • CCX01 • X1
p3 = refl

p4 : CX02 • CCX12 • CX12 • CCX01 • SWAP02 ≈ X1 • CCX12 • CCX01 • X1 • CX10
p4 = by-assoc-and (under (ε) (ε) B3908.proved) Eq.refl Eq.refl

p5 : CX02 • CCX12 • CX12 • CCX01 • SWAP02 ≈ X1 • CCX12 • CCX01 • X1 • CX10
p5 = trans p4 (refl)

p6 : CX10 • X1 • CCX12 • CCX01 • X1 ≈ X1 • CCX12 • CCX01 • X1 • CX10
p6 = trans (sym p3) (trans p2 p5)

proved : CX10 • X1 • CCX12 • CCX01 • X1 ≈ X1 • CCX12 • CCX01 • X1 • CX10
proved = p6
