{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Proofs.KB0040 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (SWAP01 ; X0 ; X1 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r028 ; refl ; sym ; trans ; module Eq)
open K

p0 : X1 ≈ SWAP01 • X0 • SWAP01
p0 = by-assoc-and (axiom r028) Eq.refl Eq.refl

p1 : X1 ≈ X1
p1 = refl

p2 : SWAP01 • X0 • SWAP01 ≈ SWAP01 • X0 • SWAP01
p2 = refl

p3 : X1 ≈ SWAP01 • X0 • SWAP01
p3 = trans (sym p1) (trans p0 p2)

p4 : SWAP01 • X0 • SWAP01 ≈ X1
p4 = sym p3

proved : SWAP01 • X0 • SWAP01 ≈ X1
proved = p4
