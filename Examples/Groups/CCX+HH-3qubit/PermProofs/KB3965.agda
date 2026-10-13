{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB3965 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0160 as B160
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0657 as B657

p0 : CX02 • X0 • CX02 • CCX01 • CCX12 • X1 ≈ CX02 • X0 • CCX12 • X1 • CCX01
p0 = by-assoc-and (under (CX02 • X0) (ε) B657.proved) Eq.refl Eq.refl

p1 : CX02 • X0 • CX02 • CCX01 • CCX12 • X1 ≈ X0 • X2 • CCX01 • CCX12 • X1
p1 = by-assoc-and (under (ε) (CCX01 • CCX12 • X1) B160.proved) Eq.refl Eq.refl

p2 : CX02 • X0 • CCX12 • X1 • CCX01 ≈ X0 • X2 • CCX01 • CCX12 • X1
p2 = trans (sym p0) p1

p3 : CX02 • X0 • CCX12 • X1 • CCX01 ≈ CX02 • X0 • CCX12 • X1 • CCX01
p3 = refl

p4 : X0 • X2 • CCX01 • CCX12 • X1 ≈ X0 • X2 • CCX01 • CCX12 • X1
p4 = refl

p5 : CX02 • X0 • CCX12 • X1 • CCX01 ≈ X0 • X2 • CCX01 • CCX12 • X1
p5 = trans (sym p3) (trans p2 p4)

proved : CX02 • X0 • CCX12 • X1 • CCX01 ≈ X0 • X2 • CCX01 • CCX12 • X1
proved = p5
