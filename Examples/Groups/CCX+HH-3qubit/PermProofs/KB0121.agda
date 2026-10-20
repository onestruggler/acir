{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0121 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX12 ; X0 ; _•_ ; _≈_ ; refl ; sym ; trans)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.drel98 as Tdrel98
p0 : X0 • CX12 • CCX01 ≈ CCX01 • X0
p0 = Tdrel98.proved

p1 : X0 • CX12 • CCX01 ≈ X0 • CX12 • CCX01
p1 = refl

p2 : CCX01 • X0 ≈ CCX01 • X0
p2 = refl

p3 : X0 • CX12 • CCX01 ≈ CCX01 • X0
p3 = trans (sym p1) (trans p0 p2)

proved : X0 • CX12 • CCX01 ≈ CCX01 • X0
proved = p3
