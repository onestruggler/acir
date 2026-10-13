{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0670 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0141 as B141
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0337 as B337

p0 : CCX02 • CX10 • CCX12 • CX12 ≈ CX10 • CCX12 • CCX02 • CX12
p0 = by-assoc-and (under (ε) (CX12) B337.proved) Eq.refl Eq.refl

p1 : CCX02 • CX10 • CCX12 • CX12 ≈ CCX02 • CX12 • CCX12
p1 = by-assoc-and (under (CCX02) (ε) B141.proved) Eq.refl Eq.refl

p2 : CX10 • CCX12 • CCX02 • CX12 ≈ CCX02 • CX12 • CCX12
p2 = trans (sym p0) p1

p3 : CX10 • CCX12 • CCX02 • CX12 ≈ CX10 • CCX12 • CCX02 • CX12
p3 = refl

p4 : CCX02 • CX12 • CCX12 ≈ CCX02 • CX12 • CCX12
p4 = refl

p5 : CX10 • CCX12 • CCX02 • CX12 ≈ CCX02 • CX12 • CCX12
p5 = trans (sym p3) (trans p2 p4)

proved : CX10 • CCX12 • CCX02 • CX12 ≈ CCX02 • CX12 • CCX12
proved = p5
