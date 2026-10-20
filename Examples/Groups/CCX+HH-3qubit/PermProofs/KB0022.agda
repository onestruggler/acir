{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0022 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; X2 ; _•_ ; _≈_ ; refl ; sym ; trans)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_CX_d as Tbifunct_X_CX_d
p0 : CX01 • X2 ≈ X2 • CX01
p0 = Tbifunct_X_CX_d.proved

p1 : CX01 • X2 ≈ CX01 • X2
p1 = refl

p2 : X2 • CX01 ≈ X2 • CX01
p2 = refl

p3 : CX01 • X2 ≈ X2 • CX01
p3 = trans (sym p1) (trans p0 p2)

proved : CX01 • X2 ≈ X2 • CX01
proved = p3
