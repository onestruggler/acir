{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0137 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX01 ; CX02 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0037 as B37

import Examples.Groups.CCX+HH-3qubit.Tietze.drel141 as Tdrel141
p0 : CX01 • CCX01 ≈ CCX01 • CX02 • CX01
p0 = Tdrel141.proved

p1 : CX01 • CCX01 ≈ CX01 • CCX01
p1 = refl

p2 : CCX01 • CX02 • CX01 ≈ CX02 • CCX01 • CX01
p2 = by-assoc-and (under (ε) (CX01) B37.proved) Eq.refl Eq.refl

p3 : CCX01 • CX02 • CX01 ≈ CX02 • CCX01 • CX01
p3 = trans p2 (refl)

p4 : CX01 • CCX01 ≈ CX02 • CCX01 • CX01
p4 = trans (sym p1) (trans p0 p3)

p5 : CX02 • CCX01 • CX01 ≈ CX01 • CCX01
p5 = sym p4

proved : CX02 • CCX01 • CX01 ≈ CX01 • CCX01
proved = p5
