{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0326 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX12 ; CX02 ; CX20 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0014 as B14
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0212 as B212
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0218 as B218

p0 : CCX12 • CCX01 • CCX12 • CCX12 ≈ CX20 • CCX01 • CX20 • CCX12
p0 = by-assoc-and (under (ε) (CCX12) B212.proved) Eq.refl Eq.refl

p1 : CCX12 • CCX01 • CCX12 • CCX12 ≈ CCX12 • CCX01
p1 = by-assoc-and (under (CCX12 • CCX01) (ε) B14.proved) Eq.refl Eq.refl

p2 : CX20 • CCX01 • CX20 • CCX12 ≈ CCX12 • CCX01
p2 = trans (sym p0) p1

p3 : CX20 • CCX01 • CX20 • CCX12 ≈ CX02 • CCX12 • CX02 • CCX12
p3 = by-assoc-and (under (ε) (CCX12) B218.proved) Eq.refl Eq.refl

p4 : CX20 • CCX01 • CX20 • CCX12 ≈ CX02 • CCX12 • CX02 • CCX12
p4 = trans p3 (refl)

p5 : CCX12 • CCX01 ≈ CCX12 • CCX01
p5 = refl

p6 : CX02 • CCX12 • CX02 • CCX12 ≈ CCX12 • CCX01
p6 = trans (sym p4) (trans p2 p5)

proved : CX02 • CCX12 • CX02 • CCX12 ≈ CCX12 • CCX01
proved = p6
