{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0407 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CX01 ; CX02 ; CX21 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0038 as B38
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0039 as B39
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0119 as B119
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0126 as B126

p0 : CCX02 • CX01 • CX02 • CX21 ≈ CCX02 • CX21 • CX02
p0 = by-assoc-and (under (CCX02) (ε) B126.proved) Eq.refl Eq.refl

p1 : CCX02 • CX01 • CX02 • CX21 ≈ CX01 • CCX02 • CX02 • CX21
p1 = by-assoc-and (under (ε) (CX02 • CX21) B38.proved) Eq.refl Eq.refl

p2 : CCX02 • CX21 • CX02 ≈ CX01 • CCX02 • CX02 • CX21
p2 = trans (sym p0) p1

p3 : CCX02 • CX21 • CX02 ≈ CX21 • CCX02 • CX02
p3 = by-assoc-and (under (ε) (CX02) B39.proved) Eq.refl Eq.refl

p4 : CCX02 • CX21 • CX02 ≈ CX21 • CCX02 • CX02
p4 = trans p3 (refl)

p5 : CX01 • CCX02 • CX02 • CX21 ≈ CX02 • CCX02 • CX21
p5 = by-assoc-and (under (ε) (CX21) B119.proved) Eq.refl Eq.refl

p6 : CX02 • CCX02 • CX21 ≈ CX02 • CX21 • CCX02
p6 = by-assoc-and (under (CX02) (ε) B39.proved) Eq.refl Eq.refl

p7 : CX01 • CCX02 • CX02 • CX21 ≈ CX02 • CX21 • CCX02
p7 = trans p5 (trans p6 (refl))

p8 : CX21 • CCX02 • CX02 ≈ CX02 • CX21 • CCX02
p8 = trans (sym p4) (trans p2 p7)

proved : CX21 • CCX02 • CX02 ≈ CX02 • CX21 • CCX02
proved = p8
