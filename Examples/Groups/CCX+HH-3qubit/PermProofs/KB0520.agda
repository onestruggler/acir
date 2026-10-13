{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0520 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0029 as B29
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0167 as B167

p0 : CCX01 • X2 • CCX12 • X2 ≈ CCX01 • CX10 • CCX12
p0 = by-assoc-and (under (CCX01) (ε) B167.proved) Eq.refl Eq.refl

p1 : CCX01 • X2 • CCX12 • X2 ≈ X2 • CCX01 • CCX12 • X2
p1 = by-assoc-and (under (ε) (CCX12 • X2) B29.proved) Eq.refl Eq.refl

p2 : CCX01 • CX10 • CCX12 ≈ X2 • CCX01 • CCX12 • X2
p2 = trans (sym p0) p1

p3 : CCX01 • CX10 • CCX12 ≈ CCX01 • CX10 • CCX12
p3 = refl

p4 : X2 • CCX01 • CCX12 • X2 ≈ X2 • CCX01 • CCX12 • X2
p4 = refl

p5 : CCX01 • CX10 • CCX12 ≈ X2 • CCX01 • CCX12 • X2
p5 = trans (sym p3) (trans p2 p4)

p6 : X2 • CCX01 • CCX12 • X2 ≈ CCX01 • CX10 • CCX12
p6 = sym p5

proved : X2 • CCX01 • CCX12 • X2 ≈ CCX01 • CX10 • CCX12
proved = p6
