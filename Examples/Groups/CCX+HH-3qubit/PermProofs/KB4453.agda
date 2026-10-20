{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB4453 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CCX12 ; CX01 ; CX02 ; CX10 ; CX12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0504 as B504
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0972 as B972

p0 : CCX02 • CX12 • CX01 • CCX12 • CX01 ≈ CCX02 • CX10 • CX12 • CCX02 • CX10
p0 = by-assoc-and (under (CCX02) (ε) B972.proved) Eq.refl Eq.refl

p1 : CCX02 • CX12 • CX01 • CCX12 • CX01 ≈ CX02 • CCX02 • CX12 • CCX12 • CX01
p1 = by-assoc-and (under (ε) (CCX12 • CX01) B504.proved) Eq.refl Eq.refl

p2 : CCX02 • CX10 • CX12 • CCX02 • CX10 ≈ CX02 • CCX02 • CX12 • CCX12 • CX01
p2 = trans (sym p0) p1

p3 : CCX02 • CX10 • CX12 • CCX02 • CX10 ≈ CCX02 • CX10 • CX12 • CCX02 • CX10
p3 = refl

p4 : CX02 • CCX02 • CX12 • CCX12 • CX01 ≈ CX02 • CCX02 • CX12 • CCX12 • CX01
p4 = refl

p5 : CCX02 • CX10 • CX12 • CCX02 • CX10 ≈ CX02 • CCX02 • CX12 • CCX12 • CX01
p5 = trans (sym p3) (trans p2 p4)

proved : CCX02 • CX10 • CX12 • CCX02 • CX10 ≈ CX02 • CCX02 • CX12 • CCX12 • CX01
proved = p5
