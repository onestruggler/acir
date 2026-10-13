{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB5198 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0029 as B29
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0055 as B55
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1377 as B1377

p0 : CCX02 • CCX01 • X0 • SWAP12 • X2 ≈ X0 • CX12 • CCX02 • CCX01 • X2
p0 = by-assoc-and (under (ε) (X2) B1377.proved) Eq.refl Eq.refl

p1 : CCX02 • CCX01 • X0 • SWAP12 • X2 ≈ CCX02 • CCX01 • X0 • X1 • SWAP12
p1 = by-assoc-and (under (CCX02 • CCX01 • X0) (ε) B55.proved) Eq.refl Eq.refl

p2 : X0 • CX12 • CCX02 • CCX01 • X2 ≈ CCX02 • CCX01 • X0 • X1 • SWAP12
p2 = trans (sym p0) p1

p3 : X0 • CX12 • CCX02 • CCX01 • X2 ≈ X0 • CX12 • CCX02 • X2 • CCX01
p3 = by-assoc-and (under (X0 • CX12 • CCX02) (ε) B29.proved) Eq.refl Eq.refl

p4 : X0 • CX12 • CCX02 • CCX01 • X2 ≈ X0 • CX12 • CCX02 • X2 • CCX01
p4 = trans p3 (refl)

p5 : CCX02 • CCX01 • X0 • X1 • SWAP12 ≈ CCX02 • CCX01 • X0 • X1 • SWAP12
p5 = refl

p6 : X0 • CX12 • CCX02 • X2 • CCX01 ≈ CCX02 • CCX01 • X0 • X1 • SWAP12
p6 = trans (sym p4) (trans p2 p5)

p7 : CCX02 • CCX01 • X0 • X1 • SWAP12 ≈ X0 • CX12 • CCX02 • X2 • CCX01
p7 = sym p6

proved : CCX02 • CCX01 • X0 • X1 • SWAP12 ≈ X0 • CX12 • CCX02 • X2 • CCX01
proved = p7
