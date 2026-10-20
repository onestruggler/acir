{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0018 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (X0 ; X2 ; _•_ ; _≈_ ; refl ; sym ; trans)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_b as Tbifunct_X_b
p0 : X0 • X2 ≈ X2 • X0
p0 = Tbifunct_X_b.proved

p1 : X0 • X2 ≈ X0 • X2
p1 = refl

p2 : X2 • X0 ≈ X2 • X0
p2 = refl

p3 : X0 • X2 ≈ X2 • X0
p3 = trans (sym p1) (trans p0 p2)

p4 : X2 • X0 ≈ X0 • X2
p4 = sym p3

proved : X2 • X0 ≈ X0 • X2
proved = p4
