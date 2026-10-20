{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0037 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX02 ; _•_ ; _≈_ ; refl ; sym ; trans)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.drel91 as Tdrel91
p0 : CCX01 • CX02 ≈ CX02 • CCX01
p0 = Tdrel91.proved

p1 : CCX01 • CX02 ≈ CCX01 • CX02
p1 = refl

p2 : CX02 • CCX01 ≈ CX02 • CCX01
p2 = refl

p3 : CCX01 • CX02 ≈ CX02 • CCX01
p3 = trans (sym p1) (trans p0 p2)

proved : CCX01 • CX02 ≈ CX02 • CCX01
proved = p3
