{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0295 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CCX12 ; CX20 ; CX21 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0179 as B179
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0209 as B209

p0 : CCX02 • CX20 • CX21 • CCX12 ≈ CX20 • CCX02 • CCX12
p0 = by-assoc-and (under (ε) (CCX12) B209.proved) Eq.refl Eq.refl

p1 : CCX02 • CX20 • CX21 • CCX12 ≈ CCX02 • CCX12 • CX21
p1 = by-assoc-and (under (CCX02) (ε) B179.proved) Eq.refl Eq.refl

p2 : CX20 • CCX02 • CCX12 ≈ CCX02 • CCX12 • CX21
p2 = trans (sym p0) p1

p3 : CX20 • CCX02 • CCX12 ≈ CX20 • CCX02 • CCX12
p3 = refl

p4 : CCX02 • CCX12 • CX21 ≈ CCX02 • CCX12 • CX21
p4 = refl

p5 : CX20 • CCX02 • CCX12 ≈ CCX02 • CCX12 • CX21
p5 = trans (sym p3) (trans p2 p4)

p6 : CCX02 • CCX12 • CX21 ≈ CX20 • CCX02 • CCX12
p6 = sym p5

proved : CCX02 • CCX12 • CX21 ≈ CX20 • CCX02 • CCX12
proved = p6
