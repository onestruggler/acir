{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0003 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (X1 ; _•_ ; _≈_ ; refl ; sym ; trans ; ε)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.elim_X1 as Telim_X1
p0 : X1 • X1 ≈ ε
p0 = Telim_X1.proved

p1 : X1 • X1 ≈ X1 • X1
p1 = refl

p2 : ε ≈ ε
p2 = refl

p3 : X1 • X1 ≈ ε
p3 = trans (sym p1) (trans p0 p2)

proved : X1 • X1 ≈ ε
proved = p3
