{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1332 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0105 as B105
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0327 as B327
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0530 as B530
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0572 as B572

p0 : CCX12 • X1 • CX02 • CX20 • CCX12 ≈ X1 • CCX12 • SWAP02 • CCX12
p0 = by-assoc-and (under (ε) (CCX12) B572.proved) Eq.refl Eq.refl

p1 : CCX12 • X1 • CX02 • CX20 • CCX12 ≈ CCX12 • CX02 • CCX12 • X1
p1 = by-assoc-and (under (CCX12) (ε) B530.proved) Eq.refl Eq.refl

p2 : X1 • CCX12 • SWAP02 • CCX12 ≈ CCX12 • CX02 • CCX12 • X1
p2 = trans (sym p0) p1

p3 : X1 • CCX12 • SWAP02 • CCX12 ≈ X1 • CCX12 • CCX01 • SWAP02
p3 = by-assoc-and (under (X1 • CCX12) (ε) B105.proved) Eq.refl Eq.refl

p4 : X1 • CCX12 • SWAP02 • CCX12 ≈ X1 • CCX12 • CCX01 • SWAP02
p4 = trans p3 (refl)

p5 : CCX12 • CX02 • CCX12 • X1 ≈ CX02 • CCX12 • CCX01 • X1
p5 = by-assoc-and (under (ε) (X1) B327.proved) Eq.refl Eq.refl

p6 : CCX12 • CX02 • CCX12 • X1 ≈ CX02 • CCX12 • CCX01 • X1
p6 = trans p5 (refl)

p7 : X1 • CCX12 • CCX01 • SWAP02 ≈ CX02 • CCX12 • CCX01 • X1
p7 = trans (sym p4) (trans p2 p6)

p8 : CX02 • CCX12 • CCX01 • X1 ≈ X1 • CCX12 • CCX01 • SWAP02
p8 = sym p7

proved : CX02 • CCX12 • CCX01 • X1 ≈ X1 • CCX12 • CCX01 • SWAP02
proved = p8
