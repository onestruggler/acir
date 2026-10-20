{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Proofs.KB0238 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; X0 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Proofs.KB0000 as B0
import Examples.Groups.CCX+HH-3qubit.Proofs.KB0235 as B235

p0 : X0 • X0 • CX01 • X0 ≈ X0 • CX01 • X1
p0 = by-assoc-and (under (X0) (ε) B235.proved) Eq.refl Eq.refl

p1 : X0 • X0 • CX01 • X0 ≈ CX01 • X0
p1 = by-assoc-and (under (ε) (CX01 • X0) B0.proved) Eq.refl Eq.refl

p2 : X0 • CX01 • X1 ≈ CX01 • X0
p2 = trans (sym p0) p1

p3 : X0 • CX01 • X1 ≈ X0 • CX01 • X1
p3 = refl

p4 : CX01 • X0 ≈ CX01 • X0
p4 = refl

p5 : X0 • CX01 • X1 ≈ CX01 • X0
p5 = trans (sym p3) (trans p2 p4)

proved : X0 • CX01 • X1 ≈ CX01 • X0
proved = p5
