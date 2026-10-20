{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0126 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX02 ; CX21 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0025 as B25
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0030 as B30

import Examples.Groups.CCX+HH-3qubit.Tietze.drel110 as Tdrel110
p0 : CX21 • CX02 ≈ CX02 • CX21 • CX01
p0 = Tdrel110.proved

p1 : CX21 • CX02 ≈ CX21 • CX02
p1 = refl

p2 : CX02 • CX21 • CX01 ≈ CX02 • CX01 • CX21
p2 = by-assoc-and (under (CX02) (ε) B30.proved) Eq.refl Eq.refl

p3 : CX02 • CX01 • CX21 ≈ CX01 • CX02 • CX21
p3 = by-assoc-and (under (ε) (CX21) B25.proved) Eq.refl Eq.refl

p4 : CX02 • CX21 • CX01 ≈ CX01 • CX02 • CX21
p4 = trans p2 (trans p3 (refl))

p5 : CX21 • CX02 ≈ CX01 • CX02 • CX21
p5 = trans (sym p1) (trans p0 p4)

p6 : CX01 • CX02 • CX21 ≈ CX21 • CX02
p6 = sym p5

proved : CX01 • CX02 • CX21 ≈ CX21 • CX02
proved = p6
