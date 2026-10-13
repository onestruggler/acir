{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1474 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0167 as B167
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0223 as B223
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0280 as B280

p0 : CCX01 • X0 • X2 • CCX12 • X2 ≈ X2 • CCX01 • X0 • CCX12 • X2
p0 = by-assoc-and (under (ε) (CCX12 • X2) B223.proved) Eq.refl Eq.refl

p1 : CCX01 • X0 • X2 • CCX12 • X2 ≈ CCX01 • X0 • CX10 • CCX12
p1 = by-assoc-and (under (CCX01 • X0) (ε) B167.proved) Eq.refl Eq.refl

p2 : X2 • CCX01 • X0 • CCX12 • X2 ≈ CCX01 • X0 • CX10 • CCX12
p2 = trans (sym p0) p1

p3 : X2 • CCX01 • X0 • CCX12 • X2 ≈ X2 • CCX01 • X0 • CCX12 • X2
p3 = refl

p4 : CCX01 • X0 • CX10 • CCX12 ≈ X0 • CX10 • CCX01 • CCX12
p4 = by-assoc-and (under (ε) (CCX12) B280.proved) Eq.refl Eq.refl

p5 : CCX01 • X0 • CX10 • CCX12 ≈ X0 • CX10 • CCX01 • CCX12
p5 = trans p4 (refl)

p6 : X2 • CCX01 • X0 • CCX12 • X2 ≈ X0 • CX10 • CCX01 • CCX12
p6 = trans (sym p3) (trans p2 p5)

proved : X2 • CCX01 • X0 • CCX12 • X2 ≈ X0 • CX10 • CCX01 • CCX12
proved = p6
