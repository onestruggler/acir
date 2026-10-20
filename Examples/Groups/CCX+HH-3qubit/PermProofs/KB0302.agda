{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0302 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX20 ; CX21 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0013 as B13
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0030 as B30
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0300 as B300

p0 : CX20 • CX01 • CX20 • CX01 • CX01 ≈ CX21 • CX01
p0 = by-assoc-and (under (ε) (CX01) B300.proved) Eq.refl Eq.refl

p1 : CX20 • CX01 • CX20 • CX01 • CX01 ≈ CX20 • CX01 • CX20
p1 = by-assoc-and (under (CX20 • CX01 • CX20) (ε) B13.proved) Eq.refl Eq.refl

p2 : CX21 • CX01 ≈ CX20 • CX01 • CX20
p2 = trans (sym p0) p1

p3 : CX21 • CX01 ≈ CX01 • CX21
p3 = by-assoc-and (under (ε) (ε) B30.proved) Eq.refl Eq.refl

p4 : CX21 • CX01 ≈ CX01 • CX21
p4 = trans p3 (refl)

p5 : CX20 • CX01 • CX20 ≈ CX20 • CX01 • CX20
p5 = refl

p6 : CX01 • CX21 ≈ CX20 • CX01 • CX20
p6 = trans (sym p4) (trans p2 p5)

p7 : CX20 • CX01 • CX20 ≈ CX01 • CX21
p7 = sym p6

proved : CX20 • CX01 • CX20 ≈ CX01 • CX21
proved = p7
