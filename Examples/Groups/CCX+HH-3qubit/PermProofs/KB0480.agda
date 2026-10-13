{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0480 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0027 as B27
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0037 as B37
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0152 as B152

p0 : CCX01 • X0 • CCX01 • CX02 ≈ X0 • CX12 • CX02
p0 = by-assoc-and (under (ε) (CX02) B152.proved) Eq.refl Eq.refl

p1 : CCX01 • X0 • CCX01 • CX02 ≈ CCX01 • X0 • CX02 • CCX01
p1 = by-assoc-and (under (CCX01 • X0) (ε) B37.proved) Eq.refl Eq.refl

p2 : X0 • CX12 • CX02 ≈ CCX01 • X0 • CX02 • CCX01
p2 = trans (sym p0) p1

p3 : X0 • CX12 • CX02 ≈ X0 • CX02 • CX12
p3 = by-assoc-and (under (X0) (ε) B27.proved) Eq.refl Eq.refl

p4 : X0 • CX12 • CX02 ≈ X0 • CX02 • CX12
p4 = trans p3 (refl)

p5 : CCX01 • X0 • CX02 • CCX01 ≈ CCX01 • X0 • CX02 • CCX01
p5 = refl

p6 : X0 • CX02 • CX12 ≈ CCX01 • X0 • CX02 • CCX01
p6 = trans (sym p4) (trans p2 p5)

p7 : CCX01 • X0 • CX02 • CCX01 ≈ X0 • CX02 • CX12
p7 = sym p6

proved : CCX01 • X0 • CX02 • CCX01 ≈ X0 • CX02 • CX12
proved = p7
