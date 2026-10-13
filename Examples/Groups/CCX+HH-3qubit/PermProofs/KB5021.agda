{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB5021 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0036 as B36
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0055 as B55
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1273 as B1273
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1329 as B1329
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB5019 as B5019

p0 : CCX01 • CCX02 • X0 • CX12 • X2 ≈ CX12 • CCX02 • CCX01 • X0 • X2
p0 = by-assoc-and (under (ε) (X2) B1273.proved) Eq.refl Eq.refl

p1 : CCX01 • CCX02 • X0 • CX12 • X2 ≈ CCX01 • CCX02 • X0 • X2 • CX12
p1 = by-assoc-and (under (CCX01 • CCX02 • X0) (ε) B36.proved) Eq.refl Eq.refl

p2 : CX12 • CCX02 • CCX01 • X0 • X2 ≈ CCX01 • CCX02 • X0 • X2 • CX12
p2 = trans (sym p0) p1

p3 : CX12 • CCX02 • CCX01 • X0 • X2 ≈ X0 • CCX02 • CCX01 • SWAP12 • X2
p3 = by-assoc-and (under (ε) (X2) B1329.proved) Eq.refl Eq.refl

p4 : X0 • CCX02 • CCX01 • SWAP12 • X2 ≈ X0 • CCX02 • CCX01 • X1 • SWAP12
p4 = by-assoc-and (under (X0 • CCX02 • CCX01) (ε) B55.proved) Eq.refl Eq.refl

p5 : CX12 • CCX02 • CCX01 • X0 • X2 ≈ X0 • CCX02 • CCX01 • X1 • SWAP12
p5 = trans p3 (trans p4 (refl))

p6 : CCX01 • CCX02 • X0 • X2 • CX12 ≈ CX12 • CCX02 • X2 • CCX01 • X0
p6 = by-assoc-and (under (ε) (ε) B5019.proved) Eq.refl Eq.refl

p7 : CCX01 • CCX02 • X0 • X2 • CX12 ≈ CX12 • CCX02 • X2 • CCX01 • X0
p7 = trans p6 (refl)

p8 : X0 • CCX02 • CCX01 • X1 • SWAP12 ≈ CX12 • CCX02 • X2 • CCX01 • X0
p8 = trans (sym p5) (trans p2 p7)

p9 : CX12 • CCX02 • X2 • CCX01 • X0 ≈ X0 • CCX02 • CCX01 • X1 • SWAP12
p9 = sym p8

proved : CX12 • CCX02 • X2 • CCX01 • X0 ≈ X0 • CCX02 • CCX01 • X1 • SWAP12
proved = p9
