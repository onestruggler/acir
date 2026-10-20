{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Proofs.KB0233 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; X0 ; X1 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r002 ; refl ; sym ; trans ; module Eq)
open K

p0 : X1 ≈ CX01 • X0 • CX01 • X0
p0 = by-assoc-and (axiom r002) Eq.refl Eq.refl

p1 : X1 ≈ X1
p1 = refl

p2 : CX01 • X0 • CX01 • X0 ≈ CX01 • X0 • CX01 • X0
p2 = refl

p3 : X1 ≈ CX01 • X0 • CX01 • X0
p3 = trans (sym p1) (trans p0 p2)

p4 : CX01 • X0 • CX01 • X0 ≈ X1
p4 = sym p3

proved : CX01 • X0 • CX01 • X0 ≈ X1
proved = p4
