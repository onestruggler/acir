{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0036 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX12 ; X2 ; _•_ ; _≈_ ; refl ; sym ; trans)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.drel84 as Tdrel84
p0 : X2 • CX12 ≈ CX12 • X2
p0 = Tdrel84.proved

p1 : X2 • CX12 ≈ X2 • CX12
p1 = refl

p2 : CX12 • X2 ≈ CX12 • X2
p2 = refl

p3 : X2 • CX12 ≈ CX12 • X2
p3 = trans (sym p1) (trans p0 p2)

p4 : CX12 • X2 ≈ X2 • CX12
p4 = sym p3

proved : CX12 • X2 ≈ X2 • CX12
proved = p4
