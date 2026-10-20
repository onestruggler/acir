{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0023 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX02 ; X1 ; _•_ ; _≈_ ; refl ; sym ; trans)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_CX_e as Tbifunct_X_CX_e
p0 : CX02 • X1 ≈ X1 • CX02
p0 = Tbifunct_X_CX_e.proved

p1 : CX02 • X1 ≈ CX02 • X1
p1 = refl

p2 : X1 • CX02 ≈ X1 • CX02
p2 = refl

p3 : CX02 • X1 ≈ X1 • CX02
p3 = trans (sym p1) (trans p0 p2)

proved : CX02 • X1 ≈ X1 • CX02
proved = p3
