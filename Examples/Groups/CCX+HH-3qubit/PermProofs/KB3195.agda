{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB3195 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX02 ; CX20 ; CX21 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0211 as B211
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0330 as B330
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1457 as B1457

p0 : CCX01 • CCX12 • CCX01 • CX21 • CCX02 ≈ CCX01 • CCX12 • CX21 • CCX02 • CCX01
p0 = by-assoc-and (under (CCX01 • CCX12) (ε) B330.proved) Eq.refl Eq.refl

p1 : CCX01 • CCX12 • CCX01 • CX21 • CCX02 ≈ CX02 • CCX12 • CX02 • CX21 • CCX02
p1 = by-assoc-and (under (ε) (CX21 • CCX02) B211.proved) Eq.refl Eq.refl

p2 : CCX01 • CCX12 • CX21 • CCX02 • CCX01 ≈ CX02 • CCX12 • CX02 • CX21 • CCX02
p2 = trans (sym p0) p1

p3 : CCX01 • CCX12 • CX21 • CCX02 • CCX01 ≈ CCX01 • CCX12 • CX21 • CCX02 • CCX01
p3 = refl

p4 : CX02 • CCX12 • CX02 • CX21 • CCX02 ≈ CX20 • CCX01 • CCX02 • CX20
p4 = by-assoc-and (under (ε) (ε) B1457.proved) Eq.refl Eq.refl

p5 : CX02 • CCX12 • CX02 • CX21 • CCX02 ≈ CX20 • CCX01 • CCX02 • CX20
p5 = trans p4 (refl)

p6 : CCX01 • CCX12 • CX21 • CCX02 • CCX01 ≈ CX20 • CCX01 • CCX02 • CX20
p6 = trans (sym p3) (trans p2 p5)

proved : CCX01 • CCX12 • CX21 • CCX02 • CCX01 ≈ CX20 • CCX01 • CCX02 • CX20
proved = p6
