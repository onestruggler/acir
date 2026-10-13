{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1275 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0046 as B46
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0047 as B47
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0336 as B336

p0 : CCX12 • CCX02 • CX10 • X0 ≈ CX10 • CCX02 • CCX12 • X0
p0 = by-assoc-and (under (ε) (X0) B336.proved) Eq.refl Eq.refl

p1 : CCX12 • CCX02 • CX10 • X0 ≈ CCX12 • CCX02 • X0 • CX10
p1 = by-assoc-and (under (CCX12 • CCX02) (ε) B47.proved) Eq.refl Eq.refl

p2 : CX10 • CCX02 • CCX12 • X0 ≈ CCX12 • CCX02 • X0 • CX10
p2 = trans (sym p0) p1

p3 : CX10 • CCX02 • CCX12 • X0 ≈ CX10 • CCX02 • X0 • CCX12
p3 = by-assoc-and (under (CX10 • CCX02) (ε) B46.proved) Eq.refl Eq.refl

p4 : CX10 • CCX02 • CCX12 • X0 ≈ CX10 • CCX02 • X0 • CCX12
p4 = trans p3 (refl)

p5 : CCX12 • CCX02 • X0 • CX10 ≈ CCX12 • CCX02 • X0 • CX10
p5 = refl

p6 : CX10 • CCX02 • X0 • CCX12 ≈ CCX12 • CCX02 • X0 • CX10
p6 = trans (sym p4) (trans p2 p5)

p7 : CCX12 • CCX02 • X0 • CX10 ≈ CX10 • CCX02 • X0 • CCX12
p7 = sym p6

proved : CCX12 • CCX02 • X0 • CX10 ≈ CX10 • CCX02 • X0 • CCX12
proved = p7
