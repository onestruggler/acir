{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0021 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX10 ; X2 ; _•_ ; _≈_ ; refl ; sym ; trans)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_CX_c as Tbifunct_X_CX_c
p0 : CX10 • X2 ≈ X2 • CX10
p0 = Tbifunct_X_CX_c.proved

p1 : CX10 • X2 ≈ CX10 • X2
p1 = refl

p2 : X2 • CX10 ≈ X2 • CX10
p2 = refl

p3 : CX10 • X2 ≈ X2 • CX10
p3 = trans (sym p1) (trans p0 p2)

proved : CX10 • X2 ≈ X2 • CX10
proved = p3
