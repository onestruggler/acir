{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0039 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CX21 ; _•_ ; _≈_ ; refl ; sym ; trans)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.drel93 as Tdrel93
p0 : CCX02 • CX21 ≈ CX21 • CCX02
p0 = Tdrel93.proved

p1 : CCX02 • CX21 ≈ CCX02 • CX21
p1 = refl

p2 : CX21 • CCX02 ≈ CX21 • CCX02
p2 = refl

p3 : CCX02 • CX21 ≈ CX21 • CCX02
p3 = trans (sym p1) (trans p0 p2)

proved : CCX02 • CX21 ≈ CX21 • CCX02
proved = p3
