{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0303 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX20 ; CX21 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0013 as B13
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0301 as B301

p0 : CX01 • CX01 • CX20 • CX01 ≈ CX01 • CX20 • CX21
p0 = by-assoc-and (under (CX01) (ε) B301.proved) Eq.refl Eq.refl

p1 : CX01 • CX01 • CX20 • CX01 ≈ CX20 • CX01
p1 = by-assoc-and (under (ε) (CX20 • CX01) B13.proved) Eq.refl Eq.refl

p2 : CX01 • CX20 • CX21 ≈ CX20 • CX01
p2 = trans (sym p0) p1

p3 : CX01 • CX20 • CX21 ≈ CX01 • CX20 • CX21
p3 = refl

p4 : CX20 • CX01 ≈ CX20 • CX01
p4 = refl

p5 : CX01 • CX20 • CX21 ≈ CX20 • CX01
p5 = trans (sym p3) (trans p2 p4)

proved : CX01 • CX20 • CX21 ≈ CX20 • CX01
proved = p5
