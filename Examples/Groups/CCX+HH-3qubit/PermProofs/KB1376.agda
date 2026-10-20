{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1376 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CX12 ; SWAP12 ; X0 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0001 as B1
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0818 as B818

p0 : CX12 • CCX02 • CCX01 • SWAP12 • SWAP12 ≈ X0 • CCX02 • CCX01 • X0 • SWAP12
p0 = by-assoc-and (under (ε) (SWAP12) B818.proved) Eq.refl Eq.refl

p1 : CX12 • CCX02 • CCX01 • SWAP12 • SWAP12 ≈ CX12 • CCX02 • CCX01
p1 = by-assoc-and (under (CX12 • CCX02 • CCX01) (ε) B1.proved) Eq.refl Eq.refl

p2 : X0 • CCX02 • CCX01 • X0 • SWAP12 ≈ CX12 • CCX02 • CCX01
p2 = trans (sym p0) p1

p3 : X0 • CCX02 • CCX01 • X0 • SWAP12 ≈ X0 • CCX02 • CCX01 • X0 • SWAP12
p3 = refl

p4 : CX12 • CCX02 • CCX01 ≈ CX12 • CCX02 • CCX01
p4 = refl

p5 : X0 • CCX02 • CCX01 • X0 • SWAP12 ≈ CX12 • CCX02 • CCX01
p5 = trans (sym p3) (trans p2 p4)

proved : X0 • CCX02 • CCX01 • X0 • SWAP12 ≈ CX12 • CCX02 • CCX01
proved = p5
