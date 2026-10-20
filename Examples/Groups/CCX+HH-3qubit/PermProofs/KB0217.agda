{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0217 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CX12 ; CX21 ; _•_ ; _≈_ ; refl ; sym ; trans)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.cflip0 as Tcflip0
p0 : CX21 • CCX01 • CX21 ≈ CX12 • CCX02 • CX12
p0 = Tcflip0.proved

p1 : CX21 • CCX01 • CX21 ≈ CX21 • CCX01 • CX21
p1 = refl

p2 : CX12 • CCX02 • CX12 ≈ CX12 • CCX02 • CX12
p2 = refl

p3 : CX21 • CCX01 • CX21 ≈ CX12 • CCX02 • CX12
p3 = trans (sym p1) (trans p0 p2)

proved : CX21 • CCX01 • CX21 ≈ CX12 • CCX02 • CX12
proved = p3
