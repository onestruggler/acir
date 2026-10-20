{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB3874 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CX12 ; CX21 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0145 as B145
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0623 as B623
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0913 as B913

p0 : CX12 • X1 • CX12 • CCX02 • X0 • CCX01 ≈ CX12 • X1 • CCX01 • CCX02 • X0
p0 = by-assoc-and (under (CX12 • X1) (ε) B623.proved) Eq.refl Eq.refl

p1 : CX12 • X1 • CX12 • CCX02 • X0 • CCX01 ≈ X1 • X2 • CCX02 • X0 • CCX01
p1 = by-assoc-and (under (ε) (CCX02 • X0 • CCX01) B145.proved) Eq.refl Eq.refl

p2 : CX12 • X1 • CCX01 • CCX02 • X0 ≈ X1 • X2 • CCX02 • X0 • CCX01
p2 = trans (sym p0) p1

p3 : CX12 • X1 • CCX01 • CCX02 • X0 ≈ CX12 • X1 • CCX01 • CCX02 • X0
p3 = refl

p4 : X1 • X2 • CCX02 • X0 • CCX01 ≈ X0 • CX21 • X2 • CCX02 • CCX01
p4 = by-assoc-and (under (ε) (CCX01) B913.proved) Eq.refl Eq.refl

p5 : X1 • X2 • CCX02 • X0 • CCX01 ≈ X0 • CX21 • X2 • CCX02 • CCX01
p5 = trans p4 (refl)

p6 : CX12 • X1 • CCX01 • CCX02 • X0 ≈ X0 • CX21 • X2 • CCX02 • CCX01
p6 = trans (sym p3) (trans p2 p5)

proved : CX12 • X1 • CCX01 • CCX02 • X0 ≈ X0 • CX21 • X2 • CCX02 • CCX01
proved = p6
