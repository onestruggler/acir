{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0024 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX20 ; X1 ; _•_ ; _≈_ ; refl ; sym ; trans)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_CX_f as Tbifunct_X_CX_f
p0 : CX20 • X1 ≈ X1 • CX20
p0 = Tbifunct_X_CX_f.proved

p1 : CX20 • X1 ≈ CX20 • X1
p1 = refl

p2 : X1 • CX20 ≈ X1 • CX20
p2 = refl

p3 : CX20 • X1 ≈ X1 • CX20
p3 = trans (sym p1) (trans p0 p2)

proved : CX20 • X1 ≈ X1 • CX20
proved = p3
