{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB5022 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0018 as B18
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0047 as B47
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0097 as B97
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1274 as B1274
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1310 as B1310

p0 : CCX12 • CCX02 • X2 • CX10 • X0 ≈ CX10 • CCX02 • CCX12 • X2 • X0
p0 = by-assoc-and (under (ε) (X0) B1274.proved) Eq.refl Eq.refl

p1 : CCX12 • CCX02 • X2 • CX10 • X0 ≈ CCX12 • CCX02 • X2 • X0 • CX10
p1 = by-assoc-and (under (CCX12 • CCX02 • X2) (ε) B47.proved) Eq.refl Eq.refl

p2 : CX10 • CCX02 • CCX12 • X2 • X0 ≈ CCX12 • CCX02 • X2 • X0 • CX10
p2 = trans (sym p0) p1

p3 : CX10 • CCX02 • CCX12 • X2 • X0 ≈ X2 • CCX02 • CCX12 • SWAP01 • X0
p3 = by-assoc-and (under (ε) (X0) B1310.proved) Eq.refl Eq.refl

p4 : X2 • CCX02 • CCX12 • SWAP01 • X0 ≈ X2 • CCX02 • CCX12 • X1 • SWAP01
p4 = by-assoc-and (under (X2 • CCX02 • CCX12) (ε) B97.proved) Eq.refl Eq.refl

p5 : CX10 • CCX02 • CCX12 • X2 • X0 ≈ X2 • CCX02 • CCX12 • X1 • SWAP01
p5 = trans p3 (trans p4 (refl))

p6 : CCX12 • CCX02 • X2 • X0 • CX10 ≈ CCX12 • CCX02 • X0 • X2 • CX10
p6 = by-assoc-and (under (CCX12 • CCX02) (CX10) B18.proved) Eq.refl Eq.refl

p7 : CCX12 • CCX02 • X2 • X0 • CX10 ≈ CCX12 • CCX02 • X0 • X2 • CX10
p7 = trans p6 (refl)

p8 : X2 • CCX02 • CCX12 • X1 • SWAP01 ≈ CCX12 • CCX02 • X0 • X2 • CX10
p8 = trans (sym p5) (trans p2 p7)

p9 : CCX12 • CCX02 • X0 • X2 • CX10 ≈ X2 • CCX02 • CCX12 • X1 • SWAP01
p9 = sym p8

proved : CCX12 • CCX02 • X0 • X2 • CX10 ≈ X2 • CCX02 • CCX12 • X1 • SWAP01
proved = p9
