{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1352 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX12 ; CX20 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0029 as B29
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1257 as B1257

p0 : CCX01 • CX20 • CCX01 • X2 ≈ CX20 • CCX01 • CCX12 • X2
p0 = by-assoc-and (under (ε) (X2) B1257.proved) Eq.refl Eq.refl

p1 : CCX01 • CX20 • CCX01 • X2 ≈ CCX01 • CX20 • X2 • CCX01
p1 = by-assoc-and (under (CCX01 • CX20) (ε) B29.proved) Eq.refl Eq.refl

p2 : CX20 • CCX01 • CCX12 • X2 ≈ CCX01 • CX20 • X2 • CCX01
p2 = trans (sym p0) p1

p3 : CX20 • CCX01 • CCX12 • X2 ≈ CX20 • CCX01 • CCX12 • X2
p3 = refl

p4 : CCX01 • CX20 • X2 • CCX01 ≈ CCX01 • CX20 • X2 • CCX01
p4 = refl

p5 : CX20 • CCX01 • CCX12 • X2 ≈ CCX01 • CX20 • X2 • CCX01
p5 = trans (sym p3) (trans p2 p4)

p6 : CCX01 • CX20 • X2 • CCX01 ≈ CX20 • CCX01 • CCX12 • X2
p6 = sym p5

proved : CCX01 • CX20 • X2 • CCX01 ≈ CX20 • CCX01 • CCX12 • X2
proved = p6
