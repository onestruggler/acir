{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0170 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX12 ; CX20 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0009 as B9
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0024 as B24
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0132 as B132

p0 : CX20 • CX20 • CCX12 • X1 ≈ CX20 • X1 • CCX12
p0 = by-assoc-and (under (CX20) (ε) B132.proved) Eq.refl Eq.refl

p1 : CX20 • CX20 • CCX12 • X1 ≈ CCX12 • X1
p1 = by-assoc-and (under (ε) (CCX12 • X1) B9.proved) Eq.refl Eq.refl

p2 : CX20 • X1 • CCX12 ≈ CCX12 • X1
p2 = trans (sym p0) p1

p3 : CX20 • X1 • CCX12 ≈ X1 • CX20 • CCX12
p3 = by-assoc-and (under (ε) (CCX12) B24.proved) Eq.refl Eq.refl

p4 : CX20 • X1 • CCX12 ≈ X1 • CX20 • CCX12
p4 = trans p3 (refl)

p5 : CCX12 • X1 ≈ CCX12 • X1
p5 = refl

p6 : X1 • CX20 • CCX12 ≈ CCX12 • X1
p6 = trans (sym p4) (trans p2 p5)

proved : X1 • CX20 • CCX12 ≈ CCX12 • X1
proved = p6
