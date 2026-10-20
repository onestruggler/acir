{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB3095 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX10 ; X0 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0219 as B219
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0280 as B280

p0 : CCX01 • X0 • CX10 • CCX02 • CX10 ≈ X0 • CX10 • CCX01 • CCX02 • CX10
p0 = by-assoc-and (under (ε) (CCX02 • CX10) B280.proved) Eq.refl Eq.refl

p1 : CCX01 • X0 • CX10 • CCX02 • CX10 ≈ CCX01 • X0 • CX01 • CCX12 • CX01
p1 = by-assoc-and (under (CCX01 • X0) (ε) B219.proved) Eq.refl Eq.refl

p2 : X0 • CX10 • CCX01 • CCX02 • CX10 ≈ CCX01 • X0 • CX01 • CCX12 • CX01
p2 = trans (sym p0) p1

p3 : X0 • CX10 • CCX01 • CCX02 • CX10 ≈ X0 • CX10 • CCX01 • CCX02 • CX10
p3 = refl

p4 : CCX01 • X0 • CX01 • CCX12 • CX01 ≈ CCX01 • X0 • CX01 • CCX12 • CX01
p4 = refl

p5 : X0 • CX10 • CCX01 • CCX02 • CX10 ≈ CCX01 • X0 • CX01 • CCX12 • CX01
p5 = trans (sym p3) (trans p2 p4)

p6 : CCX01 • X0 • CX01 • CCX12 • CX01 ≈ X0 • CX10 • CCX01 • CCX02 • CX10
p6 = sym p5

proved : CCX01 • X0 • CX01 • CCX12 • CX01 ≈ X0 • CX10 • CCX01 • CCX02 • CX10
proved = p6
