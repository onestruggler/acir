{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1378 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CCX12 ; CX01 ; SWAP01 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0000 as B0
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0821 as B821

p0 : CX01 • CCX12 • CCX02 • SWAP01 • SWAP01 ≈ X2 • CCX12 • CCX02 • X2 • SWAP01
p0 = by-assoc-and (under (ε) (SWAP01) B821.proved) Eq.refl Eq.refl

p1 : CX01 • CCX12 • CCX02 • SWAP01 • SWAP01 ≈ CX01 • CCX12 • CCX02
p1 = by-assoc-and (under (CX01 • CCX12 • CCX02) (ε) B0.proved) Eq.refl Eq.refl

p2 : X2 • CCX12 • CCX02 • X2 • SWAP01 ≈ CX01 • CCX12 • CCX02
p2 = trans (sym p0) p1

p3 : X2 • CCX12 • CCX02 • X2 • SWAP01 ≈ X2 • CCX12 • CCX02 • X2 • SWAP01
p3 = refl

p4 : CX01 • CCX12 • CCX02 ≈ CX01 • CCX12 • CCX02
p4 = refl

p5 : X2 • CCX12 • CCX02 • X2 • SWAP01 ≈ CX01 • CCX12 • CCX02
p5 = trans (sym p3) (trans p2 p4)

proved : X2 • CCX12 • CCX02 • X2 • SWAP01 ≈ CX01 • CCX12 • CCX02
proved = p5
