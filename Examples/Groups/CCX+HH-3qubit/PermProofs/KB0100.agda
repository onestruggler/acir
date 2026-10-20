{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0100 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX02 ; CX12 ; SWAP01 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r030 ; refl ; sym ; trans ; module Eq)
open K

p0 : CX12 ≈ SWAP01 • CX02 • SWAP01
p0 = by-assoc-and (axiom r030) Eq.refl Eq.refl

p1 : CX12 ≈ CX12
p1 = refl

p2 : SWAP01 • CX02 • SWAP01 ≈ SWAP01 • CX02 • SWAP01
p2 = refl

p3 : CX12 ≈ SWAP01 • CX02 • SWAP01
p3 = trans (sym p1) (trans p0 p2)

p4 : SWAP01 • CX02 • SWAP01 ≈ CX12
p4 = sym p3

proved : SWAP01 • CX02 • SWAP01 ≈ CX12
proved = p4
