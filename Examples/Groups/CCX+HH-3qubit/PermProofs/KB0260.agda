{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0260 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX02 ; CX20 ; SWAP02 ; X0 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0033 as B33
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0086 as B86
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0093 as B93

p0 : SWAP02 • CX02 • X2 ≈ CX02 • CX20 • X2
p0 = by-assoc-and (under (ε) (X2) B86.proved) Eq.refl Eq.refl

p1 : SWAP02 • CX02 • X2 ≈ SWAP02 • X2 • CX02
p1 = by-assoc-and (under (SWAP02) (ε) B33.proved) Eq.refl Eq.refl

p2 : CX02 • CX20 • X2 ≈ SWAP02 • X2 • CX02
p2 = trans (sym p0) p1

p3 : CX02 • CX20 • X2 ≈ CX02 • CX20 • X2
p3 = refl

p4 : SWAP02 • X2 • CX02 ≈ X0 • SWAP02 • CX02
p4 = by-assoc-and (under (ε) (CX02) B93.proved) Eq.refl Eq.refl

p5 : X0 • SWAP02 • CX02 ≈ X0 • CX02 • CX20
p5 = by-assoc-and (under (X0) (ε) B86.proved) Eq.refl Eq.refl

p6 : SWAP02 • X2 • CX02 ≈ X0 • CX02 • CX20
p6 = trans p4 (trans p5 (refl))

p7 : CX02 • CX20 • X2 ≈ X0 • CX02 • CX20
p7 = trans (sym p3) (trans p2 p6)

proved : CX02 • CX20 • X2 ≈ X0 • CX02 • CX20
proved = p7
