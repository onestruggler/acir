{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1310 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CCX12 ; CX01 ; CX10 ; SWAP01 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0188 as B188
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0389 as B389
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1277 as B1277

p0 : CCX02 • X2 • CX01 • CCX12 • SWAP01 ≈ CCX02 • CX10 • CCX02 • X2
p0 = by-assoc-and (under (CCX02) (ε) B389.proved) Eq.refl Eq.refl

p1 : CCX02 • X2 • CX01 • CCX12 • SWAP01 ≈ X2 • CCX02 • CCX12 • SWAP01
p1 = by-assoc-and (under (ε) (CCX12 • SWAP01) B188.proved) Eq.refl Eq.refl

p2 : CCX02 • CX10 • CCX02 • X2 ≈ X2 • CCX02 • CCX12 • SWAP01
p2 = trans (sym p0) p1

p3 : CCX02 • CX10 • CCX02 • X2 ≈ CX10 • CCX02 • CCX12 • X2
p3 = by-assoc-and (under (ε) (X2) B1277.proved) Eq.refl Eq.refl

p4 : CCX02 • CX10 • CCX02 • X2 ≈ CX10 • CCX02 • CCX12 • X2
p4 = trans p3 (refl)

p5 : X2 • CCX02 • CCX12 • SWAP01 ≈ X2 • CCX02 • CCX12 • SWAP01
p5 = refl

p6 : CX10 • CCX02 • CCX12 • X2 ≈ X2 • CCX02 • CCX12 • SWAP01
p6 = trans (sym p4) (trans p2 p5)

proved : CX10 • CCX02 • CCX12 • X2 ≈ X2 • CCX02 • CCX12 • SWAP01
proved = p6
