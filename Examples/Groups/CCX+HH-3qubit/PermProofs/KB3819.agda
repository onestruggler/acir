{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB3819 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0153 as B153
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0308 as B308
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0604 as B604
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0795 as B795
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0817 as B817

p0 : X2 • CX02 • CCX02 • X0 • CCX01 • X0 ≈ CCX02 • X0 • CX02 • CCX01 • X0
p0 = by-assoc-and (under (ε) (CCX01 • X0) B604.proved) Eq.refl Eq.refl

p1 : X2 • CX02 • CCX02 • X0 • CCX01 • X0 ≈ X2 • CX02 • CCX02 • CX12 • CCX01
p1 = by-assoc-and (under (X2 • CX02 • CCX02) (ε) B153.proved) Eq.refl Eq.refl

p2 : CCX02 • X0 • CX02 • CCX01 • X0 ≈ X2 • CX02 • CCX02 • CX12 • CCX01
p2 = trans (sym p0) p1

p3 : CCX02 • X0 • CX02 • CCX01 • X0 ≈ CCX02 • X0 • CX02 • CCX01 • X0
p3 = refl

p4 : X2 • CX02 • CCX02 • CX12 • CCX01 ≈ X2 • CX02 • CX12 • CCX01 • CCX02
p4 = by-assoc-and (under (X2 • CX02) (ε) B308.proved) Eq.refl Eq.refl

p5 : X2 • CX02 • CX12 • CCX01 • CCX02 ≈ X1 • CX12 • CCX01 • X1 • CCX02
p5 = by-assoc-and (under (ε) (CCX02) B795.proved) Eq.refl Eq.refl

p6 : X1 • CX12 • CCX01 • X1 • CCX02 ≈ X0 • CX02 • CCX01 • X0 • CCX02
p6 = by-assoc-and (under (ε) (CCX02) B817.proved) Eq.refl Eq.refl

p7 : X2 • CX02 • CCX02 • CX12 • CCX01 ≈ X0 • CX02 • CCX01 • X0 • CCX02
p7 = trans p4 (trans p5 (trans p6 (refl)))

p8 : CCX02 • X0 • CX02 • CCX01 • X0 ≈ X0 • CX02 • CCX01 • X0 • CCX02
p8 = trans (sym p3) (trans p2 p7)

proved : CCX02 • X0 • CX02 • CCX01 • X0 ≈ X0 • CX02 • CCX01 • X0 • CCX02
proved = p8
