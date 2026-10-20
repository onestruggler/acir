{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0423 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX12 ; CX01 ; CX10 ; SWAP01 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0021 as B21
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0022 as B22
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0062 as B62
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0063 as B63
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0131 as B131

p0 : SWAP01 • CX01 • CX10 • CCX12 • X2 ≈ SWAP01 • CX01 • X2 • CCX12
p0 = by-assoc-and (under (SWAP01 • CX01) (ε) B131.proved) Eq.refl Eq.refl

p1 : SWAP01 • CX01 • CX10 • CCX12 • X2 ≈ CX01 • CCX12 • X2
p1 = by-assoc-and (under (ε) (CCX12 • X2) B62.proved) Eq.refl Eq.refl

p2 : SWAP01 • CX01 • X2 • CCX12 ≈ CX01 • CCX12 • X2
p2 = trans (sym p0) p1

p3 : SWAP01 • CX01 • X2 • CCX12 ≈ CX01 • CX10 • X2 • CCX12
p3 = by-assoc-and (under (ε) (X2 • CCX12) B63.proved) Eq.refl Eq.refl

p4 : CX01 • CX10 • X2 • CCX12 ≈ CX01 • X2 • CX10 • CCX12
p4 = by-assoc-and (under (CX01) (CCX12) B21.proved) Eq.refl Eq.refl

p5 : CX01 • X2 • CX10 • CCX12 ≈ X2 • CX01 • CX10 • CCX12
p5 = by-assoc-and (under (ε) (CX10 • CCX12) B22.proved) Eq.refl Eq.refl

p6 : SWAP01 • CX01 • X2 • CCX12 ≈ X2 • CX01 • CX10 • CCX12
p6 = trans p3 (trans p4 (trans p5 (refl)))

p7 : CX01 • CCX12 • X2 ≈ CX01 • CCX12 • X2
p7 = refl

p8 : X2 • CX01 • CX10 • CCX12 ≈ CX01 • CCX12 • X2
p8 = trans (sym p6) (trans p2 p7)

proved : X2 • CX01 • CX10 • CCX12 ≈ CX01 • CCX12 • X2
proved = p8
