{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1228 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX20 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0022 as B22
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0139 as B139
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0316 as B316

p0 : X1 • CX01 • X0 • X2 • CX20 ≈ X1 • CX01 • CX20 • X2
p0 = by-assoc-and (under (X1 • CX01) (ε) B316.proved) Eq.refl Eq.refl

p1 : X1 • CX01 • X0 • X2 • CX20 ≈ X0 • CX01 • X2 • CX20
p1 = by-assoc-and (under (ε) (X2 • CX20) B139.proved) Eq.refl Eq.refl

p2 : X1 • CX01 • CX20 • X2 ≈ X0 • CX01 • X2 • CX20
p2 = trans (sym p0) p1

p3 : X1 • CX01 • CX20 • X2 ≈ X1 • CX01 • CX20 • X2
p3 = refl

p4 : X0 • CX01 • X2 • CX20 ≈ X0 • X2 • CX01 • CX20
p4 = by-assoc-and (under (X0) (CX20) B22.proved) Eq.refl Eq.refl

p5 : X0 • CX01 • X2 • CX20 ≈ X0 • X2 • CX01 • CX20
p5 = trans p4 (refl)

p6 : X1 • CX01 • CX20 • X2 ≈ X0 • X2 • CX01 • CX20
p6 = trans (sym p3) (trans p2 p5)

proved : X1 • CX01 • CX20 • X2 ≈ X0 • X2 • CX01 • CX20
proved = p6
