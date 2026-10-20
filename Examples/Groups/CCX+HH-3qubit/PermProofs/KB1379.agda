{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1379 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CCX12 ; CX01 ; SWAP01 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0004 as B4
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1378 as B1378

p0 : X2 • X2 • CCX12 • CCX02 • X2 • SWAP01 ≈ X2 • CX01 • CCX12 • CCX02
p0 = by-assoc-and (under (X2) (ε) B1378.proved) Eq.refl Eq.refl

p1 : X2 • X2 • CCX12 • CCX02 • X2 • SWAP01 ≈ CCX12 • CCX02 • X2 • SWAP01
p1 = by-assoc-and (under (ε) (CCX12 • CCX02 • X2 • SWAP01) B4.proved) Eq.refl Eq.refl

p2 : X2 • CX01 • CCX12 • CCX02 ≈ CCX12 • CCX02 • X2 • SWAP01
p2 = trans (sym p0) p1

p3 : X2 • CX01 • CCX12 • CCX02 ≈ X2 • CX01 • CCX12 • CCX02
p3 = refl

p4 : CCX12 • CCX02 • X2 • SWAP01 ≈ CCX12 • CCX02 • X2 • SWAP01
p4 = refl

p5 : X2 • CX01 • CCX12 • CCX02 ≈ CCX12 • CCX02 • X2 • SWAP01
p5 = trans (sym p3) (trans p2 p4)

p6 : CCX12 • CCX02 • X2 • SWAP01 ≈ X2 • CX01 • CCX12 • CCX02
p6 = sym p5

proved : CCX12 • CCX02 • X2 • SWAP01 ≈ X2 • CX01 • CCX12 • CCX02
proved = p6
