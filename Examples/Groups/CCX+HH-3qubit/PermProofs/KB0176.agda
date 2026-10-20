{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0176 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CX20 ; CX21 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0007 as B7
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0043 as B43
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0136 as B136

p0 : CX21 • CX21 • CCX02 • CX20 ≈ CX21 • CX20 • CCX02
p0 = by-assoc-and (under (CX21) (ε) B136.proved) Eq.refl Eq.refl

p1 : CX21 • CX21 • CCX02 • CX20 ≈ CCX02 • CX20
p1 = by-assoc-and (under (ε) (CCX02 • CX20) B7.proved) Eq.refl Eq.refl

p2 : CX21 • CX20 • CCX02 ≈ CCX02 • CX20
p2 = trans (sym p0) p1

p3 : CX21 • CX20 • CCX02 ≈ CX20 • CX21 • CCX02
p3 = by-assoc-and (under (ε) (CCX02) B43.proved) Eq.refl Eq.refl

p4 : CX21 • CX20 • CCX02 ≈ CX20 • CX21 • CCX02
p4 = trans p3 (refl)

p5 : CCX02 • CX20 ≈ CCX02 • CX20
p5 = refl

p6 : CX20 • CX21 • CCX02 ≈ CCX02 • CX20
p6 = trans (sym p4) (trans p2 p5)

proved : CX20 • CX21 • CCX02 ≈ CCX02 • CX20
proved = p6
