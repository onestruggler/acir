{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0020 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX21 ; X0 ; _•_ ; _≈_ ; refl ; sym ; trans)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_CX_b as Tbifunct_X_CX_b
p0 : CX21 • X0 ≈ X0 • CX21
p0 = Tbifunct_X_CX_b.proved

p1 : CX21 • X0 ≈ CX21 • X0
p1 = refl

p2 : X0 • CX21 ≈ X0 • CX21
p2 = refl

p3 : CX21 • X0 ≈ X0 • CX21
p3 = trans (sym p1) (trans p0 p2)

proved : CX21 • X0 ≈ X0 • CX21
proved = p3
