{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1890 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CCX12 ; CX01 ; CX02 ; CX10 ; CX12 ; SWAP01 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0032 as B32
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0112 as B112
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0141 as B141
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0261 as B261
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0376 as B376

p0 : CX01 • CCX12 • CX12 • SWAP01 • CX10 ≈ CX10 • CX02 • CCX02 • CX10
p0 = by-assoc-and (under (ε) (CX10) B376.proved) Eq.refl Eq.refl

p1 : CX01 • CCX12 • CX12 • SWAP01 • CX10 ≈ CX01 • CCX12 • CX12 • CX01 • SWAP01
p1 = by-assoc-and (under (CX01 • CCX12 • CX12) (ε) B112.proved) Eq.refl Eq.refl

p2 : CX10 • CX02 • CCX02 • CX10 ≈ CX01 • CCX12 • CX12 • CX01 • SWAP01
p2 = trans (sym p0) p1

p3 : CX10 • CX02 • CCX02 • CX10 ≈ CX10 • CX02 • CCX02 • CX10
p3 = refl

p4 : CX01 • CCX12 • CX12 • CX01 • SWAP01 ≈ CX01 • CCX12 • CX10 • CX12 • CX01
p4 = by-assoc-and (under (CX01 • CCX12) (ε) B261.proved) Eq.refl Eq.refl

p5 : CX01 • CCX12 • CX10 • CX12 • CX01 ≈ CX01 • CX10 • CCX12 • CX12 • CX01
p5 = by-assoc-and (under (CX01) (CX12 • CX01) B32.proved) Eq.refl Eq.refl

p6 : CX01 • CX10 • CCX12 • CX12 • CX01 ≈ CX01 • CX12 • CCX12 • CX01
p6 = by-assoc-and (under (CX01) (CX01) B141.proved) Eq.refl Eq.refl

p7 : CX01 • CCX12 • CX12 • CX01 • SWAP01 ≈ CX01 • CX12 • CCX12 • CX01
p7 = trans p4 (trans p5 (trans p6 (refl)))

p8 : CX10 • CX02 • CCX02 • CX10 ≈ CX01 • CX12 • CCX12 • CX01
p8 = trans (sym p3) (trans p2 p7)

proved : CX10 • CX02 • CCX02 • CX10 ≈ CX01 • CX12 • CCX12 • CX01
proved = p8
