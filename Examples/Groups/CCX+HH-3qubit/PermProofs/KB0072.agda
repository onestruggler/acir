{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0072 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX10 ; CX20 ; SWAP12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0001 as B1
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0070 as B70

p0 : SWAP12 • CX10 • SWAP12 • SWAP12 ≈ CX20 • SWAP12
p0 = by-assoc-and (under (ε) (SWAP12) B70.proved) Eq.refl Eq.refl

p1 : SWAP12 • CX10 • SWAP12 • SWAP12 ≈ SWAP12 • CX10
p1 = by-assoc-and (under (SWAP12 • CX10) (ε) B1.proved) Eq.refl Eq.refl

p2 : CX20 • SWAP12 ≈ SWAP12 • CX10
p2 = trans (sym p0) p1

p3 : CX20 • SWAP12 ≈ CX20 • SWAP12
p3 = refl

p4 : SWAP12 • CX10 ≈ SWAP12 • CX10
p4 = refl

p5 : CX20 • SWAP12 ≈ SWAP12 • CX10
p5 = trans (sym p3) (trans p2 p4)

p6 : SWAP12 • CX10 ≈ CX20 • SWAP12
p6 = sym p5

proved : SWAP12 • CX10 ≈ CX20 • SWAP12
proved = p6
