{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1107 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX12 ; CX01 ; CX10 ; SWAP01 ; X0 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0035 as B35
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0097 as B97
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0262 as B262

p0 : CCX12 • CX01 • SWAP01 • X0 ≈ CX10 • CCX12 • CX01 • X0
p0 = by-assoc-and (under (ε) (X0) B262.proved) Eq.refl Eq.refl

p1 : CCX12 • CX01 • SWAP01 • X0 ≈ CCX12 • CX01 • X1 • SWAP01
p1 = by-assoc-and (under (CCX12 • CX01) (ε) B97.proved) Eq.refl Eq.refl

p2 : CX10 • CCX12 • CX01 • X0 ≈ CCX12 • CX01 • X1 • SWAP01
p2 = trans (sym p0) p1

p3 : CX10 • CCX12 • CX01 • X0 ≈ CX10 • CCX12 • CX01 • X0
p3 = refl

p4 : CCX12 • CX01 • X1 • SWAP01 ≈ CCX12 • X1 • CX01 • SWAP01
p4 = by-assoc-and (under (CCX12) (SWAP01) B35.proved) Eq.refl Eq.refl

p5 : CCX12 • CX01 • X1 • SWAP01 ≈ CCX12 • X1 • CX01 • SWAP01
p5 = trans p4 (refl)

p6 : CX10 • CCX12 • CX01 • X0 ≈ CCX12 • X1 • CX01 • SWAP01
p6 = trans (sym p3) (trans p2 p5)

p7 : CCX12 • X1 • CX01 • SWAP01 ≈ CX10 • CCX12 • CX01 • X0
p7 = sym p6

proved : CCX12 • X1 • CX01 • SWAP01 ≈ CX10 • CCX12 • CX01 • X0
proved = p7
