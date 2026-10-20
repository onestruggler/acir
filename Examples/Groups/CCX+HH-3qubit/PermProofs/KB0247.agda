{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0247 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX10 ; CX20 ; SWAP12 ; X0 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0015 as B15
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0047 as B47
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0072 as B72

p0 : SWAP12 • CX10 • X0 ≈ CX20 • SWAP12 • X0
p0 = by-assoc-and (under (ε) (X0) B72.proved) Eq.refl Eq.refl

p1 : SWAP12 • CX10 • X0 ≈ SWAP12 • X0 • CX10
p1 = by-assoc-and (under (SWAP12) (ε) B47.proved) Eq.refl Eq.refl

p2 : CX20 • SWAP12 • X0 ≈ SWAP12 • X0 • CX10
p2 = trans (sym p0) p1

p3 : CX20 • SWAP12 • X0 ≈ CX20 • X0 • SWAP12
p3 = by-assoc-and (under (CX20) (ε) B15.proved) Eq.refl Eq.refl

p4 : CX20 • SWAP12 • X0 ≈ CX20 • X0 • SWAP12
p4 = trans p3 (refl)

p5 : SWAP12 • X0 • CX10 ≈ X0 • SWAP12 • CX10
p5 = by-assoc-and (under (ε) (CX10) B15.proved) Eq.refl Eq.refl

p6 : X0 • SWAP12 • CX10 ≈ X0 • CX20 • SWAP12
p6 = by-assoc-and (under (X0) (ε) B72.proved) Eq.refl Eq.refl

p7 : SWAP12 • X0 • CX10 ≈ X0 • CX20 • SWAP12
p7 = trans p5 (trans p6 (refl))

p8 : CX20 • X0 • SWAP12 ≈ X0 • CX20 • SWAP12
p8 = trans (sym p4) (trans p2 p7)

proved : CX20 • X0 • SWAP12 ≈ X0 • CX20 • SWAP12
proved = p8
