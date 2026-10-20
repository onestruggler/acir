{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB3182 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX20 ; CX21 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0007 as B7
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB2911 as B2911
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB3181 as B3181

p0 : CX21 • CX21 • CCX01 • CCX12 • CX21 • CCX01 ≈ CX21 • CCX01 • CCX02 • CX20 • CCX12
p0 = by-assoc-and (under (CX21) (ε) B3181.proved) Eq.refl Eq.refl

p1 : CX21 • CX21 • CCX01 • CCX12 • CX21 • CCX01 ≈ CCX01 • CCX12 • CX21 • CCX01
p1 = by-assoc-and (under (ε) (CCX01 • CCX12 • CX21 • CCX01) B7.proved) Eq.refl Eq.refl

p2 : CX21 • CCX01 • CCX02 • CX20 • CCX12 ≈ CCX01 • CCX12 • CX21 • CCX01
p2 = trans (sym p0) p1

p3 : CX21 • CCX01 • CCX02 • CX20 • CCX12 ≈ CCX02 • CCX01 • CCX12 • CX21
p3 = by-assoc-and (under (ε) (ε) B2911.proved) Eq.refl Eq.refl

p4 : CX21 • CCX01 • CCX02 • CX20 • CCX12 ≈ CCX02 • CCX01 • CCX12 • CX21
p4 = trans p3 (refl)

p5 : CCX01 • CCX12 • CX21 • CCX01 ≈ CCX01 • CCX12 • CX21 • CCX01
p5 = refl

p6 : CCX02 • CCX01 • CCX12 • CX21 ≈ CCX01 • CCX12 • CX21 • CCX01
p6 = trans (sym p4) (trans p2 p5)

proved : CCX02 • CCX01 • CCX12 • CX21 ≈ CCX01 • CCX12 • CX21 • CCX01
proved = p6
