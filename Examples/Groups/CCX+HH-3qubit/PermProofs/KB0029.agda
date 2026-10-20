{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0029 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; X2 ; _•_ ; _≈_ ; refl ; sym ; trans)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.drel26 as Tdrel26
p0 : X2 • CCX01 ≈ CCX01 • X2
p0 = Tdrel26.proved

p1 : X2 • CCX01 ≈ X2 • CCX01
p1 = refl

p2 : CCX01 • X2 ≈ CCX01 • X2
p2 = refl

p3 : X2 • CCX01 ≈ CCX01 • X2
p3 = trans (sym p1) (trans p0 p2)

p4 : CCX01 • X2 ≈ X2 • CCX01
p4 = sym p3

proved : CCX01 • X2 ≈ X2 • CCX01
proved = p4
