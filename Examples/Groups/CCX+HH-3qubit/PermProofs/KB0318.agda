{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0318 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX20 ; X0 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0012 as B12
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0316 as B316

p0 : X0 • X0 • X2 • CX20 ≈ X0 • CX20 • X2
p0 = by-assoc-and (under (X0) (ε) B316.proved) Eq.refl Eq.refl

p1 : X0 • X0 • X2 • CX20 ≈ X2 • CX20
p1 = by-assoc-and (under (ε) (X2 • CX20) B12.proved) Eq.refl Eq.refl

p2 : X0 • CX20 • X2 ≈ X2 • CX20
p2 = trans (sym p0) p1

p3 : X0 • CX20 • X2 ≈ X0 • CX20 • X2
p3 = refl

p4 : X2 • CX20 ≈ X2 • CX20
p4 = refl

p5 : X0 • CX20 • X2 ≈ X2 • CX20
p5 = trans (sym p3) (trans p2 p4)

proved : X0 • CX20 • X2 ≈ X2 • CX20
proved = p5
