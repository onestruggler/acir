{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1048 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX10 ; SWAP01 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0090 as B90
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0248 as B248

p0 : CX10 • CCX01 • SWAP01 • CCX02 ≈ CX01 • CX10 • CCX01 • CCX02
p0 = by-assoc-and (under (ε) (CCX02) B248.proved) Eq.refl Eq.refl

p1 : CX10 • CCX01 • SWAP01 • CCX02 ≈ CX10 • CCX01 • CCX12 • SWAP01
p1 = by-assoc-and (under (CX10 • CCX01) (ε) B90.proved) Eq.refl Eq.refl

p2 : CX01 • CX10 • CCX01 • CCX02 ≈ CX10 • CCX01 • CCX12 • SWAP01
p2 = trans (sym p0) p1

p3 : CX01 • CX10 • CCX01 • CCX02 ≈ CX01 • CX10 • CCX01 • CCX02
p3 = refl

p4 : CX10 • CCX01 • CCX12 • SWAP01 ≈ CX10 • CCX01 • CCX12 • SWAP01
p4 = refl

p5 : CX01 • CX10 • CCX01 • CCX02 ≈ CX10 • CCX01 • CCX12 • SWAP01
p5 = trans (sym p3) (trans p2 p4)

p6 : CX10 • CCX01 • CCX12 • SWAP01 ≈ CX01 • CX10 • CCX01 • CCX02
p6 = sym p5

proved : CX10 • CCX01 • CCX12 • SWAP01 ≈ CX01 • CX10 • CCX01 • CCX02
proved = p6
