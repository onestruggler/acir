{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0211 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX12 ; CX02 ; _•_ ; _≈_ ; refl ; sym ; trans)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.cadd0 as Tcadd0
p0 : CX02 • CCX12 • CX02 ≈ CCX01 • CCX12 • CCX01
p0 = Tcadd0.proved

p1 : CX02 • CCX12 • CX02 ≈ CX02 • CCX12 • CX02
p1 = refl

p2 : CCX01 • CCX12 • CCX01 ≈ CCX01 • CCX12 • CCX01
p2 = refl

p3 : CX02 • CCX12 • CX02 ≈ CCX01 • CCX12 • CCX01
p3 = trans (sym p1) (trans p0 p2)

p4 : CCX01 • CCX12 • CCX01 ≈ CX02 • CCX12 • CX02
p4 = sym p3

proved : CCX01 • CCX12 • CCX01 ≈ CX02 • CCX12 • CX02
proved = p4
