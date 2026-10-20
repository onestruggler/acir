{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0122 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CX01 ; X2 ; _•_ ; _≈_ ; refl ; sym ; trans)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.drel101 as Tdrel101
p0 : X2 • CX01 • CCX02 ≈ CCX02 • X2
p0 = Tdrel101.proved

p1 : X2 • CX01 • CCX02 ≈ X2 • CX01 • CCX02
p1 = refl

p2 : CCX02 • X2 ≈ CCX02 • X2
p2 = refl

p3 : X2 • CX01 • CCX02 ≈ CCX02 • X2
p3 = trans (sym p1) (trans p0 p2)

proved : X2 • CX01 • CCX02 ≈ CCX02 • X2
proved = p3
