{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB2793 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CX01 ; CX02 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0018 as B18
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0019 as B19
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0586 as B586
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0809 as B809

p0 : X2 • CX01 • X0 • CX02 • CCX02 ≈ X2 • X0 • X1 • CCX02 • CX02
p0 = by-assoc-and (under (X2) (ε) B809.proved) Eq.refl Eq.refl

p1 : X2 • CX01 • X0 • CX02 • CCX02 ≈ CX01 • CX02 • X0 • CCX02
p1 = by-assoc-and (under (ε) (CCX02) B586.proved) Eq.refl Eq.refl

p2 : X2 • X0 • X1 • CCX02 • CX02 ≈ CX01 • CX02 • X0 • CCX02
p2 = trans (sym p0) p1

p3 : X2 • X0 • X1 • CCX02 • CX02 ≈ X0 • X2 • X1 • CCX02 • CX02
p3 = by-assoc-and (under (ε) (X1 • CCX02 • CX02) B18.proved) Eq.refl Eq.refl

p4 : X0 • X2 • X1 • CCX02 • CX02 ≈ X0 • X1 • X2 • CCX02 • CX02
p4 = by-assoc-and (under (X0) (CCX02 • CX02) B19.proved) Eq.refl Eq.refl

p5 : X2 • X0 • X1 • CCX02 • CX02 ≈ X0 • X1 • X2 • CCX02 • CX02
p5 = trans p3 (trans p4 (refl))

p6 : CX01 • CX02 • X0 • CCX02 ≈ CX01 • CX02 • X0 • CCX02
p6 = refl

p7 : X0 • X1 • X2 • CCX02 • CX02 ≈ CX01 • CX02 • X0 • CCX02
p7 = trans (sym p5) (trans p2 p6)

proved : X0 • X1 • X2 • CCX02 • CX02 ≈ CX01 • CX02 • X0 • CCX02
proved = p7
