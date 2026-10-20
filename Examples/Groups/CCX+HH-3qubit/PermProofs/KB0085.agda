{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0085 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX02 ; CX20 ; SWAP02 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0008 as B8
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0084 as B84

p0 : CX02 • CX02 • CX20 • CX02 ≈ CX02 • SWAP02
p0 = by-assoc-and (under (CX02) (ε) B84.proved) Eq.refl Eq.refl

p1 : CX02 • CX02 • CX20 • CX02 ≈ CX20 • CX02
p1 = by-assoc-and (under (ε) (CX20 • CX02) B8.proved) Eq.refl Eq.refl

p2 : CX02 • SWAP02 ≈ CX20 • CX02
p2 = trans (sym p0) p1

p3 : CX02 • SWAP02 ≈ CX02 • SWAP02
p3 = refl

p4 : CX20 • CX02 ≈ CX20 • CX02
p4 = refl

p5 : CX02 • SWAP02 ≈ CX20 • CX02
p5 = trans (sym p3) (trans p2 p4)

p6 : CX20 • CX02 ≈ CX02 • SWAP02
p6 = sym p5

proved : CX20 • CX02 ≈ CX02 • SWAP02
proved = p6
