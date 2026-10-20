{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0199 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CX20 ; CX21 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0010 as B10
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0176 as B176

p0 : CX20 • CX21 • CCX02 • CCX02 ≈ CCX02 • CX20 • CCX02
p0 = by-assoc-and (under (ε) (CCX02) B176.proved) Eq.refl Eq.refl

p1 : CX20 • CX21 • CCX02 • CCX02 ≈ CX20 • CX21
p1 = by-assoc-and (under (CX20 • CX21) (ε) B10.proved) Eq.refl Eq.refl

p2 : CCX02 • CX20 • CCX02 ≈ CX20 • CX21
p2 = trans (sym p0) p1

p3 : CCX02 • CX20 • CCX02 ≈ CCX02 • CX20 • CCX02
p3 = refl

p4 : CX20 • CX21 ≈ CX20 • CX21
p4 = refl

p5 : CCX02 • CX20 • CCX02 ≈ CX20 • CX21
p5 = trans (sym p3) (trans p2 p4)

proved : CCX02 • CX20 • CCX02 ≈ CX20 • CX21
proved = p5
