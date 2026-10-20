{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1368 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CCX12 ; CX01 ; CX02 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0010 as B10
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1367 as B1367

p0 : CCX02 • CCX02 • CX02 • CCX12 • CX01 ≈ CCX02 • CX02 • CCX12 • CCX02
p0 = by-assoc-and (under (CCX02) (ε) B1367.proved) Eq.refl Eq.refl

p1 : CCX02 • CCX02 • CX02 • CCX12 • CX01 ≈ CX02 • CCX12 • CX01
p1 = by-assoc-and (under (ε) (CX02 • CCX12 • CX01) B10.proved) Eq.refl Eq.refl

p2 : CCX02 • CX02 • CCX12 • CCX02 ≈ CX02 • CCX12 • CX01
p2 = trans (sym p0) p1

p3 : CCX02 • CX02 • CCX12 • CCX02 ≈ CCX02 • CX02 • CCX12 • CCX02
p3 = refl

p4 : CX02 • CCX12 • CX01 ≈ CX02 • CCX12 • CX01
p4 = refl

p5 : CCX02 • CX02 • CCX12 • CCX02 ≈ CX02 • CCX12 • CX01
p5 = trans (sym p3) (trans p2 p4)

proved : CCX02 • CX02 • CCX12 • CCX02 ≈ CX02 • CCX12 • CX01
proved = p5
