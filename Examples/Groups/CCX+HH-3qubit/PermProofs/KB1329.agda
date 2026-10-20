{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1329 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CX12 ; CX21 ; SWAP12 ; X0 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0108 as B108
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0332 as B332
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0417 as B417
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0561 as B561

p0 : CCX02 • X0 • CX12 • CX21 • CCX02 ≈ X0 • CCX02 • SWAP12 • CCX02
p0 = by-assoc-and (under (ε) (CCX02) B561.proved) Eq.refl Eq.refl

p1 : CCX02 • X0 • CX12 • CX21 • CCX02 ≈ CCX02 • CX12 • CCX02 • X0
p1 = by-assoc-and (under (CCX02) (ε) B417.proved) Eq.refl Eq.refl

p2 : X0 • CCX02 • SWAP12 • CCX02 ≈ CCX02 • CX12 • CCX02 • X0
p2 = trans (sym p0) p1

p3 : X0 • CCX02 • SWAP12 • CCX02 ≈ X0 • CCX02 • CCX01 • SWAP12
p3 = by-assoc-and (under (X0 • CCX02) (ε) B108.proved) Eq.refl Eq.refl

p4 : X0 • CCX02 • SWAP12 • CCX02 ≈ X0 • CCX02 • CCX01 • SWAP12
p4 = trans p3 (refl)

p5 : CCX02 • CX12 • CCX02 • X0 ≈ CX12 • CCX02 • CCX01 • X0
p5 = by-assoc-and (under (ε) (X0) B332.proved) Eq.refl Eq.refl

p6 : CCX02 • CX12 • CCX02 • X0 ≈ CX12 • CCX02 • CCX01 • X0
p6 = trans p5 (refl)

p7 : X0 • CCX02 • CCX01 • SWAP12 ≈ CX12 • CCX02 • CCX01 • X0
p7 = trans (sym p4) (trans p2 p6)

p8 : CX12 • CCX02 • CCX01 • X0 ≈ X0 • CCX02 • CCX01 • SWAP12
p8 = sym p7

proved : CX12 • CCX02 • CCX01 • X0 ≈ X0 • CCX02 • CCX01 • SWAP12
proved = p8
