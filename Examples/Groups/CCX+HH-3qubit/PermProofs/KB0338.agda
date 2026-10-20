{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0338 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CCX12 ; CX01 ; CX10 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0014 as B14
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0215 as B215
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0219 as B219

p0 : CCX12 • CCX02 • CCX12 • CCX12 ≈ CX10 • CCX02 • CX10 • CCX12
p0 = by-assoc-and (under (ε) (CCX12) B215.proved) Eq.refl Eq.refl

p1 : CCX12 • CCX02 • CCX12 • CCX12 ≈ CCX12 • CCX02
p1 = by-assoc-and (under (CCX12 • CCX02) (ε) B14.proved) Eq.refl Eq.refl

p2 : CX10 • CCX02 • CX10 • CCX12 ≈ CCX12 • CCX02
p2 = trans (sym p0) p1

p3 : CX10 • CCX02 • CX10 • CCX12 ≈ CX01 • CCX12 • CX01 • CCX12
p3 = by-assoc-and (under (ε) (CCX12) B219.proved) Eq.refl Eq.refl

p4 : CX10 • CCX02 • CX10 • CCX12 ≈ CX01 • CCX12 • CX01 • CCX12
p4 = trans p3 (refl)

p5 : CCX12 • CCX02 ≈ CCX12 • CCX02
p5 = refl

p6 : CX01 • CCX12 • CX01 • CCX12 ≈ CCX12 • CCX02
p6 = trans (sym p4) (trans p2 p5)

proved : CX01 • CCX12 • CX01 • CCX12 ≈ CCX12 • CCX02
proved = p6
