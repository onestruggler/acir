{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB5250 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX02 ; CX10 ; CX12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0026 as B26
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0215 as B215
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1405 as B1405
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB4453 as B4453

p0 : CCX02 • CX12 • CCX12 • CCX02 • CCX12 ≈ CX12 • CCX12 • CCX02 • CCX01 • CCX12
p0 = by-assoc-and (under (ε) (CCX12) B1405.proved) Eq.refl Eq.refl

p1 : CCX02 • CX12 • CCX12 • CCX02 • CCX12 ≈ CCX02 • CX12 • CX10 • CCX02 • CX10
p1 = by-assoc-and (under (CCX02 • CX12) (ε) B215.proved) Eq.refl Eq.refl

p2 : CX12 • CCX12 • CCX02 • CCX01 • CCX12 ≈ CCX02 • CX12 • CX10 • CCX02 • CX10
p2 = trans (sym p0) p1

p3 : CX12 • CCX12 • CCX02 • CCX01 • CCX12 ≈ CX12 • CCX12 • CCX02 • CCX01 • CCX12
p3 = refl

p4 : CCX02 • CX12 • CX10 • CCX02 • CX10 ≈ CCX02 • CX10 • CX12 • CCX02 • CX10
p4 = by-assoc-and (under (CCX02) (CCX02 • CX10) B26.proved) Eq.refl Eq.refl

p5 : CCX02 • CX10 • CX12 • CCX02 • CX10 ≈ CX02 • CCX02 • CX12 • CCX12 • CX01
p5 = by-assoc-and (under (ε) (ε) B4453.proved) Eq.refl Eq.refl

p6 : CCX02 • CX12 • CX10 • CCX02 • CX10 ≈ CX02 • CCX02 • CX12 • CCX12 • CX01
p6 = trans p4 (trans p5 (refl))

p7 : CX12 • CCX12 • CCX02 • CCX01 • CCX12 ≈ CX02 • CCX02 • CX12 • CCX12 • CX01
p7 = trans (sym p3) (trans p2 p6)

proved : CX12 • CCX12 • CCX02 • CCX01 • CCX12 ≈ CX02 • CCX02 • CX12 • CCX12 • CX01
proved = p7
