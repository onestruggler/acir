{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB5146 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX12 ; CX20 ; CX21 ; X0 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0223 as B223
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0317 as B317
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1357 as B1357

p0 : CCX12 • CX21 • CCX01 • CX20 • X2 • CX20 ≈ CX21 • CCX01 • CCX12 • X2 • CX20
p0 = by-assoc-and (under (ε) (X2 • CX20) B1357.proved) Eq.refl Eq.refl

p1 : CCX12 • CX21 • CCX01 • CX20 • X2 • CX20 ≈ CCX12 • CX21 • CCX01 • X0 • X2
p1 = by-assoc-and (under (CCX12 • CX21 • CCX01) (ε) B317.proved) Eq.refl Eq.refl

p2 : CX21 • CCX01 • CCX12 • X2 • CX20 ≈ CCX12 • CX21 • CCX01 • X0 • X2
p2 = trans (sym p0) p1

p3 : CX21 • CCX01 • CCX12 • X2 • CX20 ≈ CX21 • CCX01 • CCX12 • X2 • CX20
p3 = refl

p4 : CCX12 • CX21 • CCX01 • X0 • X2 ≈ CCX12 • CX21 • X2 • CCX01 • X0
p4 = by-assoc-and (under (CCX12 • CX21) (ε) B223.proved) Eq.refl Eq.refl

p5 : CCX12 • CX21 • CCX01 • X0 • X2 ≈ CCX12 • CX21 • X2 • CCX01 • X0
p5 = trans p4 (refl)

p6 : CX21 • CCX01 • CCX12 • X2 • CX20 ≈ CCX12 • CX21 • X2 • CCX01 • X0
p6 = trans (sym p3) (trans p2 p5)

p7 : CCX12 • CX21 • X2 • CCX01 • X0 ≈ CX21 • CCX01 • CCX12 • X2 • CX20
p7 = sym p6

proved : CCX12 • CX21 • X2 • CCX01 • X0 ≈ CX21 • CCX01 • CCX12 • X2 • CX20
proved = p7
