{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0596 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0143 as B143
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0231 as B231

p0 : CCX02 • X0 • X1 • CX10 ≈ X1 • CCX02 • X0 • CX10
p0 = by-assoc-and (under (ε) (CX10) B231.proved) Eq.refl Eq.refl

p1 : CCX02 • X0 • X1 • CX10 ≈ CCX02 • CX10 • X1
p1 = by-assoc-and (under (CCX02) (ε) B143.proved) Eq.refl Eq.refl

p2 : X1 • CCX02 • X0 • CX10 ≈ CCX02 • CX10 • X1
p2 = trans (sym p0) p1

p3 : X1 • CCX02 • X0 • CX10 ≈ X1 • CCX02 • X0 • CX10
p3 = refl

p4 : CCX02 • CX10 • X1 ≈ CCX02 • CX10 • X1
p4 = refl

p5 : X1 • CCX02 • X0 • CX10 ≈ CCX02 • CX10 • X1
p5 = trans (sym p3) (trans p2 p4)

proved : X1 • CCX02 • X0 • CX10 ≈ CCX02 • CX10 • X1
proved = p5
