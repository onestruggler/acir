{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB3634 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0044 as B44
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0187 as B187
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0477 as B477
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0897 as B897

p0 : X1 • CCX02 • CX02 • CCX01 • X0 • CX12 ≈ CCX02 • CCX01 • X1 • X0 • CX12
p0 = by-assoc-and (under (ε) (X0 • CX12) B477.proved) Eq.refl Eq.refl

p1 : X1 • CCX02 • CX02 • CCX01 • X0 • CX12 ≈ X1 • CCX02 • CX02 • X0 • CCX01
p1 = by-assoc-and (under (X1 • CCX02 • CX02) (ε) B187.proved) Eq.refl Eq.refl

p2 : CCX02 • CCX01 • X1 • X0 • CX12 ≈ X1 • CCX02 • CX02 • X0 • CCX01
p2 = trans (sym p0) p1

p3 : CCX02 • CCX01 • X1 • X0 • CX12 ≈ CCX02 • CCX01 • X0 • X1 • CX12
p3 = by-assoc-and (under (CCX02 • CCX01) (CX12) B44.proved) Eq.refl Eq.refl

p4 : CCX02 • CCX01 • X0 • X1 • CX12 ≈ CCX02 • X0 • X2 • CCX01 • X1
p4 = by-assoc-and (under (CCX02) (ε) B897.proved) Eq.refl Eq.refl

p5 : CCX02 • CCX01 • X1 • X0 • CX12 ≈ CCX02 • X0 • X2 • CCX01 • X1
p5 = trans p3 (trans p4 (refl))

p6 : X1 • CCX02 • CX02 • X0 • CCX01 ≈ X1 • CCX02 • CX02 • X0 • CCX01
p6 = refl

p7 : CCX02 • X0 • X2 • CCX01 • X1 ≈ X1 • CCX02 • CX02 • X0 • CCX01
p7 = trans (sym p5) (trans p2 p6)

proved : CCX02 • X0 • X2 • CCX01 • X1 ≈ X1 • CCX02 • CX02 • X0 • CCX01
proved = p7
