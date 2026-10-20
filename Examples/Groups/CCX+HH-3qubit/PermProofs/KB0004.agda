{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0004 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (X2 ; _•_ ; _≈_ ; refl ; sym ; trans ; ε)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.elim_X2 as Telim_X2
p0 : X2 • X2 ≈ ε
p0 = Telim_X2.proved

p1 : X2 • X2 ≈ X2 • X2
p1 = refl

p2 : ε ≈ ε
p2 = refl

p3 : X2 • X2 ≈ ε
p3 = trans (sym p1) (trans p0 p2)

proved : X2 • X2 ≈ ε
proved = p3
