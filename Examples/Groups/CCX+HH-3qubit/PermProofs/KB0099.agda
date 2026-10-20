{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0099 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX02 ; CX20 ; SWAP02 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0002 as B2
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0098 as B98

p0 : CX02 • CX20 • SWAP02 • SWAP02 ≈ CX20 • SWAP02
p0 = by-assoc-and (under (ε) (SWAP02) B98.proved) Eq.refl Eq.refl

p1 : CX02 • CX20 • SWAP02 • SWAP02 ≈ CX02 • CX20
p1 = by-assoc-and (under (CX02 • CX20) (ε) B2.proved) Eq.refl Eq.refl

p2 : CX20 • SWAP02 ≈ CX02 • CX20
p2 = trans (sym p0) p1

p3 : CX20 • SWAP02 ≈ CX20 • SWAP02
p3 = refl

p4 : CX02 • CX20 ≈ CX02 • CX20
p4 = refl

p5 : CX20 • SWAP02 ≈ CX02 • CX20
p5 = trans (sym p3) (trans p2 p4)

proved : CX20 • SWAP02 ≈ CX02 • CX20
proved = p5
