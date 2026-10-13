{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0167 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0004 as B4
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0131 as B131

p0 : CX10 • CCX12 • X2 • X2 ≈ X2 • CCX12 • X2
p0 = by-assoc-and (under (ε) (X2) B131.proved) Eq.refl Eq.refl

p1 : CX10 • CCX12 • X2 • X2 ≈ CX10 • CCX12
p1 = by-assoc-and (under (CX10 • CCX12) (ε) B4.proved) Eq.refl Eq.refl

p2 : X2 • CCX12 • X2 ≈ CX10 • CCX12
p2 = trans (sym p0) p1

p3 : X2 • CCX12 • X2 ≈ X2 • CCX12 • X2
p3 = refl

p4 : CX10 • CCX12 ≈ CX10 • CCX12
p4 = refl

p5 : X2 • CCX12 • X2 ≈ CX10 • CCX12
p5 = trans (sym p3) (trans p2 p4)

proved : X2 • CCX12 • X2 ≈ CX10 • CCX12
proved = p5
