{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0019 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (X1 ; X2 ; _•_ ; _≈_ ; refl ; sym ; trans)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_c as Tbifunct_X_c
p0 : X1 • X2 ≈ X2 • X1
p0 = Tbifunct_X_c.proved

p1 : X1 • X2 ≈ X1 • X2
p1 = refl

p2 : X2 • X1 ≈ X2 • X1
p2 = refl

p3 : X1 • X2 ≈ X2 • X1
p3 = trans (sym p1) (trans p0 p2)

p4 : X2 • X1 ≈ X1 • X2
p4 = sym p3

proved : X2 • X1 ≈ X1 • X2
proved = p4
