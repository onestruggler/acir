{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0123 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX01 ; CX02 ; _•_ ; _≈_ ; refl ; sym ; trans)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.drel103 as Tdrel103
p0 : CCX01 • CX01 ≈ CX01 • CX02 • CCX01
p0 = Tdrel103.proved

p1 : CCX01 • CX01 ≈ CCX01 • CX01
p1 = refl

p2 : CX01 • CX02 • CCX01 ≈ CX01 • CX02 • CCX01
p2 = refl

p3 : CCX01 • CX01 ≈ CX01 • CX02 • CCX01
p3 = trans (sym p1) (trans p0 p2)

p4 : CX01 • CX02 • CCX01 ≈ CCX01 • CX01
p4 = sym p3

proved : CX01 • CX02 • CCX01 ≈ CCX01 • CX01
proved = p4
