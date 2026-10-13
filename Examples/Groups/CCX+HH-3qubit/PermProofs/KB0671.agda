{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0671 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0122 as B122
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0340 as B340

p0 : X2 • CX01 • CCX02 • CCX12 • CX01 ≈ X2 • CCX12 • CCX02
p0 = by-assoc-and (under (X2) (ε) B340.proved) Eq.refl Eq.refl

p1 : X2 • CX01 • CCX02 • CCX12 • CX01 ≈ CCX02 • X2 • CCX12 • CX01
p1 = by-assoc-and (under (ε) (CCX12 • CX01) B122.proved) Eq.refl Eq.refl

p2 : X2 • CCX12 • CCX02 ≈ CCX02 • X2 • CCX12 • CX01
p2 = trans (sym p0) p1

p3 : X2 • CCX12 • CCX02 ≈ X2 • CCX12 • CCX02
p3 = refl

p4 : CCX02 • X2 • CCX12 • CX01 ≈ CCX02 • X2 • CCX12 • CX01
p4 = refl

p5 : X2 • CCX12 • CCX02 ≈ CCX02 • X2 • CCX12 • CX01
p5 = trans (sym p3) (trans p2 p4)

p6 : CCX02 • X2 • CCX12 • CX01 ≈ X2 • CCX12 • CCX02
p6 = sym p5

proved : CCX02 • X2 • CCX12 • CX01 ≈ X2 • CCX12 • CCX02
proved = p6
