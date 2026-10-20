{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0261 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX10 ; CX12 ; SWAP01 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0026 as B26
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0088 as B88

p0 : CX12 • CX10 • CX01 ≈ CX12 • CX01 • SWAP01
p0 = by-assoc-and (under (CX12) (ε) B88.proved) Eq.refl Eq.refl

p1 : CX12 • CX10 • CX01 ≈ CX10 • CX12 • CX01
p1 = by-assoc-and (under (ε) (CX01) B26.proved) Eq.refl Eq.refl

p2 : CX12 • CX01 • SWAP01 ≈ CX10 • CX12 • CX01
p2 = trans (sym p0) p1

p3 : CX12 • CX01 • SWAP01 ≈ CX12 • CX01 • SWAP01
p3 = refl

p4 : CX10 • CX12 • CX01 ≈ CX10 • CX12 • CX01
p4 = refl

p5 : CX12 • CX01 • SWAP01 ≈ CX10 • CX12 • CX01
p5 = trans (sym p3) (trans p2 p4)

proved : CX12 • CX01 • SWAP01 ≈ CX10 • CX12 • CX01
proved = p5
