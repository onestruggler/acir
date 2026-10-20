{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1363 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CCX12 ; CX10 ; CX12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0014 as B14
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1362 as B1362

p0 : CCX12 • CCX12 • CX12 • CCX02 • CX10 ≈ CCX12 • CX12 • CCX02 • CCX12
p0 = by-assoc-and (under (CCX12) (ε) B1362.proved) Eq.refl Eq.refl

p1 : CCX12 • CCX12 • CX12 • CCX02 • CX10 ≈ CX12 • CCX02 • CX10
p1 = by-assoc-and (under (ε) (CX12 • CCX02 • CX10) B14.proved) Eq.refl Eq.refl

p2 : CCX12 • CX12 • CCX02 • CCX12 ≈ CX12 • CCX02 • CX10
p2 = trans (sym p0) p1

p3 : CCX12 • CX12 • CCX02 • CCX12 ≈ CCX12 • CX12 • CCX02 • CCX12
p3 = refl

p4 : CX12 • CCX02 • CX10 ≈ CX12 • CCX02 • CX10
p4 = refl

p5 : CCX12 • CX12 • CCX02 • CCX12 ≈ CX12 • CCX02 • CX10
p5 = trans (sym p3) (trans p2 p4)

proved : CCX12 • CX12 • CCX02 • CCX12 ≈ CX12 • CCX02 • CX10
proved = p5
