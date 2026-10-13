{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB3112 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0283 as B283
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0287 as B287

p0 : CCX12 • X2 • CX12 • CCX01 • CX01 ≈ X2 • CX12 • CCX12 • CCX01 • CX01
p0 = by-assoc-and (under (ε) (CCX01 • CX01) B287.proved) Eq.refl Eq.refl

p1 : CCX12 • X2 • CX12 • CCX01 • CX01 ≈ CCX12 • X2 • CX01 • CX12 • CCX01
p1 = by-assoc-and (under (CCX12 • X2) (ε) B283.proved) Eq.refl Eq.refl

p2 : X2 • CX12 • CCX12 • CCX01 • CX01 ≈ CCX12 • X2 • CX01 • CX12 • CCX01
p2 = trans (sym p0) p1

p3 : X2 • CX12 • CCX12 • CCX01 • CX01 ≈ X2 • CX12 • CCX12 • CCX01 • CX01
p3 = refl

p4 : CCX12 • X2 • CX01 • CX12 • CCX01 ≈ CCX12 • X2 • CX01 • CX12 • CCX01
p4 = refl

p5 : X2 • CX12 • CCX12 • CCX01 • CX01 ≈ CCX12 • X2 • CX01 • CX12 • CCX01
p5 = trans (sym p3) (trans p2 p4)

p6 : CCX12 • X2 • CX01 • CX12 • CCX01 ≈ X2 • CX12 • CCX12 • CCX01 • CX01
p6 = sym p5

proved : CCX12 • X2 • CX01 • CX12 • CCX01 ≈ X2 • CX12 • CCX12 • CCX01 • CX01
proved = p6
