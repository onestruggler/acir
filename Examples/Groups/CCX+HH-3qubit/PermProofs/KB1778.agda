{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1778 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX12 ; CX02 ; CX10 ; CX12 ; CX20 ; CX21 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0218 as B218
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0284 as B284
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0345 as B345

p0 : CX20 • CCX01 • CX20 • CX21 • CX10 ≈ CX20 • CCX01 • CX10 • CX21
p0 = by-assoc-and (under (CX20 • CCX01) (ε) B345.proved) Eq.refl Eq.refl

p1 : CX20 • CCX01 • CX20 • CX21 • CX10 ≈ CX02 • CCX12 • CX02 • CX21 • CX10
p1 = by-assoc-and (under (ε) (CX21 • CX10) B218.proved) Eq.refl Eq.refl

p2 : CX20 • CCX01 • CX10 • CX21 ≈ CX02 • CCX12 • CX02 • CX21 • CX10
p2 = trans (sym p0) p1

p3 : CX20 • CCX01 • CX10 • CX21 ≈ CX12 • CX20 • CCX01 • CX21
p3 = by-assoc-and (under (ε) (CX21) B284.proved) Eq.refl Eq.refl

p4 : CX20 • CCX01 • CX10 • CX21 ≈ CX12 • CX20 • CCX01 • CX21
p4 = trans p3 (refl)

p5 : CX02 • CCX12 • CX02 • CX21 • CX10 ≈ CX02 • CCX12 • CX02 • CX21 • CX10
p5 = refl

p6 : CX12 • CX20 • CCX01 • CX21 ≈ CX02 • CCX12 • CX02 • CX21 • CX10
p6 = trans (sym p4) (trans p2 p5)

p7 : CX02 • CCX12 • CX02 • CX21 • CX10 ≈ CX12 • CX20 • CCX01 • CX21
p7 = sym p6

proved : CX02 • CCX12 • CX02 • CX21 • CX10 ≈ CX12 • CX20 • CCX01 • CX21
proved = p7
