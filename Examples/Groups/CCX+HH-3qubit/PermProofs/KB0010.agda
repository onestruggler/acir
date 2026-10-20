{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0010 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; _•_ ; _≈_ ; refl ; sym ; trans ; ε)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CCX1 as Telim_CCX1
p0 : CCX02 • CCX02 ≈ ε
p0 = Telim_CCX1.proved

p1 : CCX02 • CCX02 ≈ CCX02 • CCX02
p1 = refl

p2 : ε ≈ ε
p2 = refl

p3 : CCX02 • CCX02 ≈ ε
p3 = trans (sym p1) (trans p0 p2)

proved : CCX02 • CCX02 ≈ ε
proved = p3
