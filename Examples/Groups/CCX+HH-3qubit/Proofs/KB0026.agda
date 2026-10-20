{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Proofs.KB0026 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX10 ; K01 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r012 ; refl ; sym ; trans ; module Eq)
open K

p0 : CX10 ≈ K01 • CX01 • K01
p0 = by-assoc-and (axiom r012) Eq.refl Eq.refl

p1 : CX10 ≈ CX10
p1 = refl

p2 : K01 • CX01 • K01 ≈ K01 • CX01 • K01
p2 = refl

p3 : CX10 ≈ K01 • CX01 • K01
p3 = trans (sym p1) (trans p0 p2)

p4 : K01 • CX01 • K01 ≈ CX10
p4 = sym p3

proved : K01 • CX01 • K01 ≈ CX10
proved = p4
