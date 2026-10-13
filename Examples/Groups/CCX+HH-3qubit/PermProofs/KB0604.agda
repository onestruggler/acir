{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0604 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0128 as B128
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0281 as B281

p0 : CCX02 • X2 • CX02 • X0 ≈ X2 • CX02 • CCX02 • X0
p0 = by-assoc-and (under (ε) (X0) B281.proved) Eq.refl Eq.refl

p1 : CCX02 • X2 • CX02 • X0 ≈ CCX02 • X0 • CX02
p1 = by-assoc-and (under (CCX02) (ε) B128.proved) Eq.refl Eq.refl

p2 : X2 • CX02 • CCX02 • X0 ≈ CCX02 • X0 • CX02
p2 = trans (sym p0) p1

p3 : X2 • CX02 • CCX02 • X0 ≈ X2 • CX02 • CCX02 • X0
p3 = refl

p4 : CCX02 • X0 • CX02 ≈ CCX02 • X0 • CX02
p4 = refl

p5 : X2 • CX02 • CCX02 • X0 ≈ CCX02 • X0 • CX02
p5 = trans (sym p3) (trans p2 p4)

proved : X2 • CX02 • CCX02 • X0 ≈ CCX02 • X0 • CX02
proved = p5
