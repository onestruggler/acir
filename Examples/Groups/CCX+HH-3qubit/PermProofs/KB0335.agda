{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0335 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CCX12 ; CX10 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0014 as B14
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0032 as B32
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0215 as B215

p0 : CCX12 • CCX12 • CCX02 • CCX12 ≈ CCX12 • CX10 • CCX02 • CX10
p0 = by-assoc-and (under (CCX12) (ε) B215.proved) Eq.refl Eq.refl

p1 : CCX12 • CCX12 • CCX02 • CCX12 ≈ CCX02 • CCX12
p1 = by-assoc-and (under (ε) (CCX02 • CCX12) B14.proved) Eq.refl Eq.refl

p2 : CCX12 • CX10 • CCX02 • CX10 ≈ CCX02 • CCX12
p2 = trans (sym p0) p1

p3 : CCX12 • CX10 • CCX02 • CX10 ≈ CX10 • CCX12 • CCX02 • CX10
p3 = by-assoc-and (under (ε) (CCX02 • CX10) B32.proved) Eq.refl Eq.refl

p4 : CCX12 • CX10 • CCX02 • CX10 ≈ CX10 • CCX12 • CCX02 • CX10
p4 = trans p3 (refl)

p5 : CCX02 • CCX12 ≈ CCX02 • CCX12
p5 = refl

p6 : CX10 • CCX12 • CCX02 • CX10 ≈ CCX02 • CCX12
p6 = trans (sym p4) (trans p2 p5)

proved : CX10 • CCX12 • CCX02 • CX10 ≈ CCX02 • CCX12
proved = p6
