{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0028 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; X1 ; _•_ ; _≈_ ; refl ; sym ; trans)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.drel25 as Tdrel25
p0 : X1 • CCX02 ≈ CCX02 • X1
p0 = Tdrel25.proved

p1 : X1 • CCX02 ≈ X1 • CCX02
p1 = refl

p2 : CCX02 • X1 ≈ CCX02 • X1
p2 = refl

p3 : X1 • CCX02 ≈ CCX02 • X1
p3 = trans (sym p1) (trans p0 p2)

p4 : CCX02 • X1 ≈ X1 • CCX02
p4 = sym p3

proved : CCX02 • X1 ≈ X1 • CCX02
proved = p4
