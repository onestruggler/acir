{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0264 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CCX12 ; CX01 ; CX10 ; SWAP01 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0038 as B38
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0063 as B63
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0090 as B90
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0228 as B228

p0 : SWAP01 • CCX02 • CX01 ≈ CCX12 • SWAP01 • CX01
p0 = by-assoc-and (under (ε) (CX01) B90.proved) Eq.refl Eq.refl

p1 : SWAP01 • CCX02 • CX01 ≈ SWAP01 • CX01 • CCX02
p1 = by-assoc-and (under (SWAP01) (ε) B38.proved) Eq.refl Eq.refl

p2 : CCX12 • SWAP01 • CX01 ≈ SWAP01 • CX01 • CCX02
p2 = trans (sym p0) p1

p3 : CCX12 • SWAP01 • CX01 ≈ CCX12 • CX01 • CX10
p3 = by-assoc-and (under (CCX12) (ε) B63.proved) Eq.refl Eq.refl

p4 : CCX12 • CX01 • CX10 ≈ CX10 • CCX12 • SWAP01
p4 = by-assoc-and (under (ε) (ε) B228.proved) Eq.refl Eq.refl

p5 : CCX12 • SWAP01 • CX01 ≈ CX10 • CCX12 • SWAP01
p5 = trans p3 (trans p4 (refl))

p6 : SWAP01 • CX01 • CCX02 ≈ CX01 • CX10 • CCX02
p6 = by-assoc-and (under (ε) (CCX02) B63.proved) Eq.refl Eq.refl

p7 : SWAP01 • CX01 • CCX02 ≈ CX01 • CX10 • CCX02
p7 = trans p6 (refl)

p8 : CX10 • CCX12 • SWAP01 ≈ CX01 • CX10 • CCX02
p8 = trans (sym p5) (trans p2 p7)

proved : CX10 • CCX12 • SWAP01 ≈ CX01 • CX10 • CCX02
proved = p8
