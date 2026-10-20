{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0081 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX02 ; SWAP12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r009 ; refl ; sym ; trans ; module Eq)
open K

p0 : CX02 ≈ SWAP12 • CX01 • SWAP12
p0 = by-assoc-and (axiom r009) Eq.refl Eq.refl

p1 : CX02 ≈ CX02
p1 = refl

p2 : SWAP12 • CX01 • SWAP12 ≈ SWAP12 • CX01 • SWAP12
p2 = refl

p3 : CX02 ≈ SWAP12 • CX01 • SWAP12
p3 = trans (sym p1) (trans p0 p2)

p4 : SWAP12 • CX01 • SWAP12 ≈ CX02
p4 = sym p3

proved : SWAP12 • CX01 • SWAP12 ≈ CX02
proved = p4
