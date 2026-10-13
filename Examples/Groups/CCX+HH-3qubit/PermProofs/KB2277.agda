{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB2277 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0407 as B407
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0511 as B511

p0 : X0 • CCX12 • CX21 • CCX02 • CX02 ≈ CCX12 • CCX02 • X0 • CX02
p0 = by-assoc-and (under (ε) (CX02) B511.proved) Eq.refl Eq.refl

p1 : X0 • CCX12 • CX21 • CCX02 • CX02 ≈ X0 • CCX12 • CX02 • CX21 • CCX02
p1 = by-assoc-and (under (X0 • CCX12) (ε) B407.proved) Eq.refl Eq.refl

p2 : CCX12 • CCX02 • X0 • CX02 ≈ X0 • CCX12 • CX02 • CX21 • CCX02
p2 = trans (sym p0) p1

p3 : CCX12 • CCX02 • X0 • CX02 ≈ CCX12 • CCX02 • X0 • CX02
p3 = refl

p4 : X0 • CCX12 • CX02 • CX21 • CCX02 ≈ X0 • CCX12 • CX02 • CX21 • CCX02
p4 = refl

p5 : CCX12 • CCX02 • X0 • CX02 ≈ X0 • CCX12 • CX02 • CX21 • CCX02
p5 = trans (sym p3) (trans p2 p4)

p6 : X0 • CCX12 • CX02 • CX21 • CCX02 ≈ CCX12 • CCX02 • X0 • CX02
p6 = sym p5

proved : X0 • CCX12 • CX02 • CX21 • CCX02 ≈ CCX12 • CCX02 • X0 • CX02
proved = p6
