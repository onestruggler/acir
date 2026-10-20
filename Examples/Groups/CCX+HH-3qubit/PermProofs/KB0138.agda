{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0138 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX12 ; CX20 ; CX21 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0040 as B40

import Examples.Groups.CCX+HH-3qubit.Tietze.drel155 as Tdrel155
p0 : CX21 • CCX12 ≈ CCX12 • CX20 • CX21
p0 = Tdrel155.proved

p1 : CX21 • CCX12 ≈ CX21 • CCX12
p1 = refl

p2 : CCX12 • CX20 • CX21 ≈ CX20 • CCX12 • CX21
p2 = by-assoc-and (under (ε) (CX21) B40.proved) Eq.refl Eq.refl

p3 : CCX12 • CX20 • CX21 ≈ CX20 • CCX12 • CX21
p3 = trans p2 (refl)

p4 : CX21 • CCX12 ≈ CX20 • CCX12 • CX21
p4 = trans (sym p1) (trans p0 p3)

p5 : CX20 • CCX12 • CX21 ≈ CX21 • CCX12
p5 = sym p4

proved : CX20 • CCX12 • CX21 ≈ CX21 • CCX12
proved = p5
