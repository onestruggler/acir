{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB4079 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0193 as B193
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0671 as B671

p0 : CCX02 • X0 • CCX02 • X2 • CCX12 • CX01 ≈ CCX02 • X0 • X2 • CCX12 • CCX02
p0 = by-assoc-and (under (CCX02 • X0) (ε) B671.proved) Eq.refl Eq.refl

p1 : CCX02 • X0 • CCX02 • X2 • CCX12 • CX01 ≈ X0 • CX21 • X2 • CCX12 • CX01
p1 = by-assoc-and (under (ε) (X2 • CCX12 • CX01) B193.proved) Eq.refl Eq.refl

p2 : CCX02 • X0 • X2 • CCX12 • CCX02 ≈ X0 • CX21 • X2 • CCX12 • CX01
p2 = trans (sym p0) p1

p3 : CCX02 • X0 • X2 • CCX12 • CCX02 ≈ CCX02 • X0 • X2 • CCX12 • CCX02
p3 = refl

p4 : X0 • CX21 • X2 • CCX12 • CX01 ≈ X0 • CX21 • X2 • CCX12 • CX01
p4 = refl

p5 : CCX02 • X0 • X2 • CCX12 • CCX02 ≈ X0 • CX21 • X2 • CCX12 • CX01
p5 = trans (sym p3) (trans p2 p4)

proved : CCX02 • X0 • X2 • CCX12 • CCX02 ≈ X0 • CX21 • X2 • CCX12 • CX01
proved = p5
