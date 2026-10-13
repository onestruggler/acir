{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0916 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0168 as B168
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0191 as B191

p0 : CX02 • X0 • X2 • CX10 • CCX12 ≈ X0 • CX02 • CX10 • CCX12
p0 = by-assoc-and (under (ε) (CX10 • CCX12) B191.proved) Eq.refl Eq.refl

p1 : CX02 • X0 • X2 • CX10 • CCX12 ≈ CX02 • X0 • CCX12 • X2
p1 = by-assoc-and (under (CX02 • X0) (ε) B168.proved) Eq.refl Eq.refl

p2 : X0 • CX02 • CX10 • CCX12 ≈ CX02 • X0 • CCX12 • X2
p2 = trans (sym p0) p1

p3 : X0 • CX02 • CX10 • CCX12 ≈ X0 • CX02 • CX10 • CCX12
p3 = refl

p4 : CX02 • X0 • CCX12 • X2 ≈ CX02 • X0 • CCX12 • X2
p4 = refl

p5 : X0 • CX02 • CX10 • CCX12 ≈ CX02 • X0 • CCX12 • X2
p5 = trans (sym p3) (trans p2 p4)

p6 : CX02 • X0 • CCX12 • X2 ≈ X0 • CX02 • CX10 • CCX12
p6 = sym p5

proved : CX02 • X0 • CCX12 • X2 ≈ X0 • CX02 • CX10 • CCX12
proved = p6
