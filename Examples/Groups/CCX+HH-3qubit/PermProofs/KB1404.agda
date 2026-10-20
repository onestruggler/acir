{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1404 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX12 ; CX20 ; CX21 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0009 as B9
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0217 as B217
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0547 as B547
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1359 as B1359

p0 : CCX12 • CCX02 • CCX01 • CX20 • CX20 ≈ CX21 • CCX01 • CCX12 • CCX02 • CX20
p0 = by-assoc-and (under (ε) (CX20) B1359.proved) Eq.refl Eq.refl

p1 : CCX12 • CCX02 • CCX01 • CX20 • CX20 ≈ CCX12 • CCX02 • CCX01
p1 = by-assoc-and (under (CCX12 • CCX02 • CCX01) (ε) B9.proved) Eq.refl Eq.refl

p2 : CX21 • CCX01 • CCX12 • CCX02 • CX20 ≈ CCX12 • CCX02 • CCX01
p2 = trans (sym p0) p1

p3 : CX21 • CCX01 • CCX12 • CCX02 • CX20 ≈ CX21 • CCX01 • CX21 • CCX12 • CCX02
p3 = by-assoc-and (under (CX21 • CCX01) (ε) B547.proved) Eq.refl Eq.refl

p4 : CX21 • CCX01 • CX21 • CCX12 • CCX02 ≈ CX12 • CCX02 • CX12 • CCX12 • CCX02
p4 = by-assoc-and (under (ε) (CCX12 • CCX02) B217.proved) Eq.refl Eq.refl

p5 : CX21 • CCX01 • CCX12 • CCX02 • CX20 ≈ CX12 • CCX02 • CX12 • CCX12 • CCX02
p5 = trans p3 (trans p4 (refl))

p6 : CCX12 • CCX02 • CCX01 ≈ CCX12 • CCX02 • CCX01
p6 = refl

p7 : CX12 • CCX02 • CX12 • CCX12 • CCX02 ≈ CCX12 • CCX02 • CCX01
p7 = trans (sym p5) (trans p2 p6)

proved : CX12 • CCX02 • CX12 • CCX12 • CCX02 ≈ CCX12 • CCX02 • CCX01
proved = p7
