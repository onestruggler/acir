{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0439 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX12 ; CX20 ; CX21 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0034 as B34
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0132 as B132
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0138 as B138

p0 : CX20 • CCX12 • CX21 • X1 ≈ CX21 • CCX12 • X1
p0 = by-assoc-and (under (ε) (X1) B138.proved) Eq.refl Eq.refl

p1 : CX20 • CCX12 • CX21 • X1 ≈ CX20 • CCX12 • X1 • CX21
p1 = by-assoc-and (under (CX20 • CCX12) (ε) B34.proved) Eq.refl Eq.refl

p2 : CX21 • CCX12 • X1 ≈ CX20 • CCX12 • X1 • CX21
p2 = trans (sym p0) p1

p3 : CX21 • CCX12 • X1 ≈ CX21 • CCX12 • X1
p3 = refl

p4 : CX20 • CCX12 • X1 • CX21 ≈ X1 • CCX12 • CX21
p4 = by-assoc-and (under (ε) (CX21) B132.proved) Eq.refl Eq.refl

p5 : CX20 • CCX12 • X1 • CX21 ≈ X1 • CCX12 • CX21
p5 = trans p4 (refl)

p6 : CX21 • CCX12 • X1 ≈ X1 • CCX12 • CX21
p6 = trans (sym p3) (trans p2 p5)

proved : CX21 • CCX12 • X1 ≈ X1 • CCX12 • CX21
proved = p6
