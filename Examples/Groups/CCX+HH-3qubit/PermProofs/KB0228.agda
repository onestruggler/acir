{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0228 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0032 as B32
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0042 as B42

p0 : CCX12 • CX10 • SWAP01 ≈ CCX12 • CX01 • CX10
p0 = by-assoc-and (under (CCX12) (ε) B42.proved) Eq.refl Eq.refl

p1 : CCX12 • CX10 • SWAP01 ≈ CX10 • CCX12 • SWAP01
p1 = by-assoc-and (under (ε) (SWAP01) B32.proved) Eq.refl Eq.refl

p2 : CCX12 • CX01 • CX10 ≈ CX10 • CCX12 • SWAP01
p2 = trans (sym p0) p1

p3 : CCX12 • CX01 • CX10 ≈ CCX12 • CX01 • CX10
p3 = refl

p4 : CX10 • CCX12 • SWAP01 ≈ CX10 • CCX12 • SWAP01
p4 = refl

p5 : CCX12 • CX01 • CX10 ≈ CX10 • CCX12 • SWAP01
p5 = trans (sym p3) (trans p2 p4)

proved : CCX12 • CX01 • CX10 ≈ CX10 • CCX12 • SWAP01
proved = p5
