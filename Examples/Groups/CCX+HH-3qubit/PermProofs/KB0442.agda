{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0442 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX02 ; X0 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0023 as B23
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0025 as B25
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0139 as B139

p0 : CX02 • X1 • CX01 • X0 ≈ CX02 • X0 • CX01
p0 = by-assoc-and (under (CX02) (ε) B139.proved) Eq.refl Eq.refl

p1 : CX02 • X1 • CX01 • X0 ≈ X1 • CX02 • CX01 • X0
p1 = by-assoc-and (under (ε) (CX01 • X0) B23.proved) Eq.refl Eq.refl

p2 : CX02 • X0 • CX01 ≈ X1 • CX02 • CX01 • X0
p2 = trans (sym p0) p1

p3 : CX02 • X0 • CX01 ≈ CX02 • X0 • CX01
p3 = refl

p4 : X1 • CX02 • CX01 • X0 ≈ X1 • CX01 • CX02 • X0
p4 = by-assoc-and (under (X1) (X0) B25.proved) Eq.refl Eq.refl

p5 : X1 • CX02 • CX01 • X0 ≈ X1 • CX01 • CX02 • X0
p5 = trans p4 (refl)

p6 : CX02 • X0 • CX01 ≈ X1 • CX01 • CX02 • X0
p6 = trans (sym p3) (trans p2 p5)

p7 : X1 • CX01 • CX02 • X0 ≈ CX02 • X0 • CX01
p7 = sym p6

proved : X1 • CX01 • CX02 • X0 ≈ CX02 • X0 • CX01
proved = p7
