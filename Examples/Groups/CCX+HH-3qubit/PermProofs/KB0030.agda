{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0030 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX21 ; _•_ ; _≈_ ; refl ; sym ; trans)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.drel41 as Tdrel41
p0 : CX01 • CX21 ≈ CX21 • CX01
p0 = Tdrel41.proved

p1 : CX01 • CX21 ≈ CX01 • CX21
p1 = refl

p2 : CX21 • CX01 ≈ CX21 • CX01
p2 = refl

p3 : CX01 • CX21 ≈ CX21 • CX01
p3 = trans (sym p1) (trans p0 p2)

p4 : CX21 • CX01 ≈ CX01 • CX21
p4 = sym p3

proved : CX21 • CX01 ≈ CX01 • CX21
proved = p4
