{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB2911 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX20 ; CX21 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0179 as B179
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1264 as B1264

p0 : CCX02 • CCX01 • CX20 • CX21 • CCX12 ≈ CX21 • CCX01 • CCX02 • CX20 • CCX12
p0 = by-assoc-and (under (ε) (CCX12) B1264.proved) Eq.refl Eq.refl

p1 : CCX02 • CCX01 • CX20 • CX21 • CCX12 ≈ CCX02 • CCX01 • CCX12 • CX21
p1 = by-assoc-and (under (CCX02 • CCX01) (ε) B179.proved) Eq.refl Eq.refl

p2 : CX21 • CCX01 • CCX02 • CX20 • CCX12 ≈ CCX02 • CCX01 • CCX12 • CX21
p2 = trans (sym p0) p1

p3 : CX21 • CCX01 • CCX02 • CX20 • CCX12 ≈ CX21 • CCX01 • CCX02 • CX20 • CCX12
p3 = refl

p4 : CCX02 • CCX01 • CCX12 • CX21 ≈ CCX02 • CCX01 • CCX12 • CX21
p4 = refl

p5 : CX21 • CCX01 • CCX02 • CX20 • CCX12 ≈ CCX02 • CCX01 • CCX12 • CX21
p5 = trans (sym p3) (trans p2 p4)

proved : CX21 • CCX01 • CCX02 • CX20 • CCX12 ≈ CCX02 • CCX01 • CCX12 • CX21
proved = p5
