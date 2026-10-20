{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0040 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX12 ; CX20 ; _•_ ; _≈_ ; refl ; sym ; trans)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.drel94 as Tdrel94
p0 : CCX12 • CX20 ≈ CX20 • CCX12
p0 = Tdrel94.proved

p1 : CCX12 • CX20 ≈ CCX12 • CX20
p1 = refl

p2 : CX20 • CCX12 ≈ CX20 • CCX12
p2 = refl

p3 : CCX12 • CX20 ≈ CX20 • CCX12
p3 = trans (sym p1) (trans p0 p2)

proved : CCX12 • CX20 ≈ CX20 • CCX12
proved = p3
