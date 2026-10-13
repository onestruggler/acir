{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0511 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0046 as B46
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0165 as B165

p0 : CCX12 • X0 • CX21 • CCX02 ≈ CCX12 • CCX02 • X0
p0 = by-assoc-and (under (CCX12) (ε) B165.proved) Eq.refl Eq.refl

p1 : CCX12 • X0 • CX21 • CCX02 ≈ X0 • CCX12 • CX21 • CCX02
p1 = by-assoc-and (under (ε) (CX21 • CCX02) B46.proved) Eq.refl Eq.refl

p2 : CCX12 • CCX02 • X0 ≈ X0 • CCX12 • CX21 • CCX02
p2 = trans (sym p0) p1

p3 : CCX12 • CCX02 • X0 ≈ CCX12 • CCX02 • X0
p3 = refl

p4 : X0 • CCX12 • CX21 • CCX02 ≈ X0 • CCX12 • CX21 • CCX02
p4 = refl

p5 : CCX12 • CCX02 • X0 ≈ X0 • CCX12 • CX21 • CCX02
p5 = trans (sym p3) (trans p2 p4)

p6 : X0 • CCX12 • CX21 • CCX02 ≈ CCX12 • CCX02 • X0
p6 = sym p5

proved : X0 • CCX12 • CX21 • CCX02 ≈ CCX12 • CCX02 • X0
proved = p6
