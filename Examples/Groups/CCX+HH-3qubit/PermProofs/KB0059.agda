{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0059 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX10 ; CX12 ; SWAP02 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0002 as B2
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0057 as B57

p0 : SWAP02 • CX12 • SWAP02 • SWAP02 ≈ CX10 • SWAP02
p0 = by-assoc-and (under (ε) (SWAP02) B57.proved) Eq.refl Eq.refl

p1 : SWAP02 • CX12 • SWAP02 • SWAP02 ≈ SWAP02 • CX12
p1 = by-assoc-and (under (SWAP02 • CX12) (ε) B2.proved) Eq.refl Eq.refl

p2 : CX10 • SWAP02 ≈ SWAP02 • CX12
p2 = trans (sym p0) p1

p3 : CX10 • SWAP02 ≈ CX10 • SWAP02
p3 = refl

p4 : SWAP02 • CX12 ≈ SWAP02 • CX12
p4 = refl

p5 : CX10 • SWAP02 ≈ SWAP02 • CX12
p5 = trans (sym p3) (trans p2 p4)

p6 : SWAP02 • CX12 ≈ CX10 • SWAP02
p6 = sym p5

proved : SWAP02 • CX12 ≈ CX10 • SWAP02
proved = p6
