{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1377 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CX12 ; SWAP12 ; X0 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0012 as B12
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1376 as B1376

p0 : X0 • X0 • CCX02 • CCX01 • X0 • SWAP12 ≈ X0 • CX12 • CCX02 • CCX01
p0 = by-assoc-and (under (X0) (ε) B1376.proved) Eq.refl Eq.refl

p1 : X0 • X0 • CCX02 • CCX01 • X0 • SWAP12 ≈ CCX02 • CCX01 • X0 • SWAP12
p1 = by-assoc-and (under (ε) (CCX02 • CCX01 • X0 • SWAP12) B12.proved) Eq.refl Eq.refl

p2 : X0 • CX12 • CCX02 • CCX01 ≈ CCX02 • CCX01 • X0 • SWAP12
p2 = trans (sym p0) p1

p3 : X0 • CX12 • CCX02 • CCX01 ≈ X0 • CX12 • CCX02 • CCX01
p3 = refl

p4 : CCX02 • CCX01 • X0 • SWAP12 ≈ CCX02 • CCX01 • X0 • SWAP12
p4 = refl

p5 : X0 • CX12 • CCX02 • CCX01 ≈ CCX02 • CCX01 • X0 • SWAP12
p5 = trans (sym p3) (trans p2 p4)

p6 : CCX02 • CCX01 • X0 • SWAP12 ≈ X0 • CX12 • CCX02 • CCX01
p6 = sym p5

proved : CCX02 • CCX01 • X0 • SWAP12 ≈ X0 • CX12 • CCX02 • CCX01
proved = p6
