{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0169 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX12 ; CX20 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0003 as B3
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0132 as B132

p0 : CX20 • CCX12 • X1 • X1 ≈ X1 • CCX12 • X1
p0 = by-assoc-and (under (ε) (X1) B132.proved) Eq.refl Eq.refl

p1 : CX20 • CCX12 • X1 • X1 ≈ CX20 • CCX12
p1 = by-assoc-and (under (CX20 • CCX12) (ε) B3.proved) Eq.refl Eq.refl

p2 : X1 • CCX12 • X1 ≈ CX20 • CCX12
p2 = trans (sym p0) p1

p3 : X1 • CCX12 • X1 ≈ X1 • CCX12 • X1
p3 = refl

p4 : CX20 • CCX12 ≈ CX20 • CCX12
p4 = refl

p5 : X1 • CCX12 • X1 ≈ CX20 • CCX12
p5 = trans (sym p3) (trans p2 p4)

proved : X1 • CCX12 • X1 ≈ CX20 • CCX12
proved = p5
