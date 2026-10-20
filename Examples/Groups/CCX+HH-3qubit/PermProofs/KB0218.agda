{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0218 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX12 ; CX02 ; CX20 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0211 as B211
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0212 as B212

import Examples.Groups.CCX+HH-3qubit.Tietze.cflip1 as Tcflip1
p0 : CCX01 • CCX12 • CCX01 ≈ CCX12 • CCX01 • CCX12
p0 = Tcflip1.proved

p1 : CCX01 • CCX12 • CCX01 ≈ CX02 • CCX12 • CX02
p1 = by-assoc-and (under (ε) (ε) B211.proved) Eq.refl Eq.refl

p2 : CCX01 • CCX12 • CCX01 ≈ CX02 • CCX12 • CX02
p2 = trans p1 (refl)

p3 : CCX12 • CCX01 • CCX12 ≈ CX20 • CCX01 • CX20
p3 = by-assoc-and (under (ε) (ε) B212.proved) Eq.refl Eq.refl

p4 : CCX12 • CCX01 • CCX12 ≈ CX20 • CCX01 • CX20
p4 = trans p3 (refl)

p5 : CX02 • CCX12 • CX02 ≈ CX20 • CCX01 • CX20
p5 = trans (sym p2) (trans p0 p4)

p6 : CX20 • CCX01 • CX20 ≈ CX02 • CCX12 • CX02
p6 = sym p5

proved : CX20 • CCX01 • CX20 ≈ CX02 • CCX12 • CX02
proved = p6
