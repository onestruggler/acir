{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0336 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0005 as B5
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0335 as B335

p0 : CX10 • CX10 • CCX12 • CCX02 • CX10 ≈ CX10 • CCX02 • CCX12
p0 = by-assoc-and (under (CX10) (ε) B335.proved) Eq.refl Eq.refl

p1 : CX10 • CX10 • CCX12 • CCX02 • CX10 ≈ CCX12 • CCX02 • CX10
p1 = by-assoc-and (under (ε) (CCX12 • CCX02 • CX10) B5.proved) Eq.refl Eq.refl

p2 : CX10 • CCX02 • CCX12 ≈ CCX12 • CCX02 • CX10
p2 = trans (sym p0) p1

p3 : CX10 • CCX02 • CCX12 ≈ CX10 • CCX02 • CCX12
p3 = refl

p4 : CCX12 • CCX02 • CX10 ≈ CCX12 • CCX02 • CX10
p4 = refl

p5 : CX10 • CCX02 • CCX12 ≈ CCX12 • CCX02 • CX10
p5 = trans (sym p3) (trans p2 p4)

p6 : CCX12 • CCX02 • CX10 ≈ CX10 • CCX02 • CCX12
p6 = sym p5

proved : CCX12 • CCX02 • CX10 ≈ CX10 • CCX02 • CCX12
proved = p6
