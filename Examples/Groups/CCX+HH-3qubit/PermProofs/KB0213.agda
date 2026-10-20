{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0213 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CX21 ; _•_ ; _≈_ ; refl ; sym ; trans)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.cadd4 as Tcadd4
p0 : CX21 • CCX01 • CX21 ≈ CCX02 • CCX01 • CCX02
p0 = Tcadd4.proved

p1 : CX21 • CCX01 • CX21 ≈ CX21 • CCX01 • CX21
p1 = refl

p2 : CCX02 • CCX01 • CCX02 ≈ CCX02 • CCX01 • CCX02
p2 = refl

p3 : CX21 • CCX01 • CX21 ≈ CCX02 • CCX01 • CCX02
p3 = trans (sym p1) (trans p0 p2)

p4 : CCX02 • CCX01 • CCX02 ≈ CX21 • CCX01 • CX21
p4 = sym p3

proved : CCX02 • CCX01 • CCX02 ≈ CX21 • CCX01 • CX21
proved = p4
