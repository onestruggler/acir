{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0087 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX10 ; SWAP01 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r013 ; refl ; sym ; trans ; module Eq)
open K

p0 : SWAP01 ≈ CX01 • CX10 • CX01
p0 = by-assoc-and (axiom r013) Eq.refl Eq.refl

p1 : SWAP01 ≈ SWAP01
p1 = refl

p2 : CX01 • CX10 • CX01 ≈ CX01 • CX10 • CX01
p2 = refl

p3 : SWAP01 ≈ CX01 • CX10 • CX01
p3 = trans (sym p1) (trans p0 p2)

p4 : CX01 • CX10 • CX01 ≈ SWAP01
p4 = sym p3

proved : CX01 • CX10 • CX01 ≈ SWAP01
proved = p4
