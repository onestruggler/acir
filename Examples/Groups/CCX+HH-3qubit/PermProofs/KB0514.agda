{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0514 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0044 as B44
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0166 as B166

p0 : X1 • X0 • CCX02 • X0 ≈ X1 • CX21 • CCX02
p0 = by-assoc-and (under (X1) (ε) B166.proved) Eq.refl Eq.refl

p1 : X1 • X0 • CCX02 • X0 ≈ X0 • X1 • CCX02 • X0
p1 = by-assoc-and (under (ε) (CCX02 • X0) B44.proved) Eq.refl Eq.refl

p2 : X1 • CX21 • CCX02 ≈ X0 • X1 • CCX02 • X0
p2 = trans (sym p0) p1

p3 : X1 • CX21 • CCX02 ≈ X1 • CX21 • CCX02
p3 = refl

p4 : X0 • X1 • CCX02 • X0 ≈ X0 • X1 • CCX02 • X0
p4 = refl

p5 : X1 • CX21 • CCX02 ≈ X0 • X1 • CCX02 • X0
p5 = trans (sym p3) (trans p2 p4)

p6 : X0 • X1 • CCX02 • X0 ≈ X1 • CX21 • CCX02
p6 = sym p5

proved : X0 • X1 • CCX02 • X0 ≈ X1 • CX21 • CCX02
proved = p6
