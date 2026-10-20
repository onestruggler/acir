{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB3825 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX01 ; CX20 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0022 as B22
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0223 as B223
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0316 as B316
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0605 as B605

p0 : X1 • CX01 • CCX01 • X0 • X2 • CX20 ≈ CCX01 • X0 • CX01 • X2 • CX20
p0 = by-assoc-and (under (ε) (X2 • CX20) B605.proved) Eq.refl Eq.refl

p1 : X1 • CX01 • CCX01 • X0 • X2 • CX20 ≈ X1 • CX01 • CCX01 • CX20 • X2
p1 = by-assoc-and (under (X1 • CX01 • CCX01) (ε) B316.proved) Eq.refl Eq.refl

p2 : CCX01 • X0 • CX01 • X2 • CX20 ≈ X1 • CX01 • CCX01 • CX20 • X2
p2 = trans (sym p0) p1

p3 : CCX01 • X0 • CX01 • X2 • CX20 ≈ CCX01 • X0 • X2 • CX01 • CX20
p3 = by-assoc-and (under (CCX01 • X0) (CX20) B22.proved) Eq.refl Eq.refl

p4 : CCX01 • X0 • X2 • CX01 • CX20 ≈ X2 • CCX01 • X0 • CX01 • CX20
p4 = by-assoc-and (under (ε) (CX01 • CX20) B223.proved) Eq.refl Eq.refl

p5 : CCX01 • X0 • CX01 • X2 • CX20 ≈ X2 • CCX01 • X0 • CX01 • CX20
p5 = trans p3 (trans p4 (refl))

p6 : X1 • CX01 • CCX01 • CX20 • X2 ≈ X1 • CX01 • CCX01 • CX20 • X2
p6 = refl

p7 : X2 • CCX01 • X0 • CX01 • CX20 ≈ X1 • CX01 • CCX01 • CX20 • X2
p7 = trans (sym p5) (trans p2 p6)

proved : X2 • CCX01 • X0 • CX01 • CX20 ≈ X1 • CX01 • CCX01 • CX20 • X2
proved = p7
