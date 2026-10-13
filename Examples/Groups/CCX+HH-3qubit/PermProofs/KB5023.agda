{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB5023 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0021 as B21
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1275 as B1275
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB5022 as B5022

p0 : CCX12 • CCX02 • X0 • CX10 • X2 ≈ CX10 • CCX02 • X0 • CCX12 • X2
p0 = by-assoc-and (under (ε) (X2) B1275.proved) Eq.refl Eq.refl

p1 : CCX12 • CCX02 • X0 • CX10 • X2 ≈ CCX12 • CCX02 • X0 • X2 • CX10
p1 = by-assoc-and (under (CCX12 • CCX02 • X0) (ε) B21.proved) Eq.refl Eq.refl

p2 : CX10 • CCX02 • X0 • CCX12 • X2 ≈ CCX12 • CCX02 • X0 • X2 • CX10
p2 = trans (sym p0) p1

p3 : CX10 • CCX02 • X0 • CCX12 • X2 ≈ CX10 • CCX02 • X0 • CCX12 • X2
p3 = refl

p4 : CCX12 • CCX02 • X0 • X2 • CX10 ≈ X2 • CCX02 • CCX12 • X1 • SWAP01
p4 = by-assoc-and (under (ε) (ε) B5022.proved) Eq.refl Eq.refl

p5 : CCX12 • CCX02 • X0 • X2 • CX10 ≈ X2 • CCX02 • CCX12 • X1 • SWAP01
p5 = trans p4 (refl)

p6 : CX10 • CCX02 • X0 • CCX12 • X2 ≈ X2 • CCX02 • CCX12 • X1 • SWAP01
p6 = trans (sym p3) (trans p2 p5)

proved : CX10 • CCX02 • X0 • CCX12 • X2 ≈ X2 • CCX02 • CCX12 • X1 • SWAP01
proved = p6
