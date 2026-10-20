{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0389 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CCX12 ; CX01 ; CX10 ; SWAP01 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0021 as B21
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0088 as B88
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0090 as B90
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0122 as B122

p0 : CX10 • X2 • CX01 • CCX02 ≈ CX10 • CCX02 • X2
p0 = by-assoc-and (under (CX10) (ε) B122.proved) Eq.refl Eq.refl

p1 : CX10 • X2 • CX01 • CCX02 ≈ X2 • CX10 • CX01 • CCX02
p1 = by-assoc-and (under (ε) (CX01 • CCX02) B21.proved) Eq.refl Eq.refl

p2 : CX10 • CCX02 • X2 ≈ X2 • CX10 • CX01 • CCX02
p2 = trans (sym p0) p1

p3 : CX10 • CCX02 • X2 ≈ CX10 • CCX02 • X2
p3 = refl

p4 : X2 • CX10 • CX01 • CCX02 ≈ X2 • CX01 • SWAP01 • CCX02
p4 = by-assoc-and (under (X2) (CCX02) B88.proved) Eq.refl Eq.refl

p5 : X2 • CX01 • SWAP01 • CCX02 ≈ X2 • CX01 • CCX12 • SWAP01
p5 = by-assoc-and (under (X2 • CX01) (ε) B90.proved) Eq.refl Eq.refl

p6 : X2 • CX10 • CX01 • CCX02 ≈ X2 • CX01 • CCX12 • SWAP01
p6 = trans p4 (trans p5 (refl))

p7 : CX10 • CCX02 • X2 ≈ X2 • CX01 • CCX12 • SWAP01
p7 = trans (sym p3) (trans p2 p6)

p8 : X2 • CX01 • CCX12 • SWAP01 ≈ CX10 • CCX02 • X2
p8 = sym p7

proved : X2 • CX01 • CCX12 • SWAP01 ≈ CX10 • CCX02 • X2
proved = p8
