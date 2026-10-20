{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0025 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX02 ; _•_ ; _≈_ ; refl ; sym ; trans)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.drel9 as Tdrel9
p0 : CX01 • CX02 ≈ CX02 • CX01
p0 = Tdrel9.proved

p1 : CX01 • CX02 ≈ CX01 • CX02
p1 = refl

p2 : CX02 • CX01 ≈ CX02 • CX01
p2 = refl

p3 : CX01 • CX02 ≈ CX02 • CX01
p3 = trans (sym p1) (trans p0 p2)

p4 : CX02 • CX01 ≈ CX01 • CX02
p4 = sym p3

proved : CX02 • CX01 ≈ CX01 • CX02
proved = p4
