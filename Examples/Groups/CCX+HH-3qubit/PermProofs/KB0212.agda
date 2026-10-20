{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0212 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX12 ; CX20 ; _•_ ; _≈_ ; refl ; sym ; trans)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.cadd3 as Tcadd3
p0 : CX20 • CCX01 • CX20 ≈ CCX12 • CCX01 • CCX12
p0 = Tcadd3.proved

p1 : CX20 • CCX01 • CX20 ≈ CX20 • CCX01 • CX20
p1 = refl

p2 : CCX12 • CCX01 • CCX12 ≈ CCX12 • CCX01 • CCX12
p2 = refl

p3 : CX20 • CCX01 • CX20 ≈ CCX12 • CCX01 • CCX12
p3 = trans (sym p1) (trans p0 p2)

p4 : CCX12 • CCX01 • CCX12 ≈ CX20 • CCX01 • CX20
p4 = sym p3

proved : CCX12 • CCX01 • CCX12 ≈ CX20 • CCX01 • CX20
proved = p4
