{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0080 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX12 ; CX21 ; SWAP12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0006 as B6
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0079 as B79

p0 : CX12 • CX12 • CX21 • CX12 ≈ CX12 • SWAP12
p0 = by-assoc-and (under (CX12) (ε) B79.proved) Eq.refl Eq.refl

p1 : CX12 • CX12 • CX21 • CX12 ≈ CX21 • CX12
p1 = by-assoc-and (under (ε) (CX21 • CX12) B6.proved) Eq.refl Eq.refl

p2 : CX12 • SWAP12 ≈ CX21 • CX12
p2 = trans (sym p0) p1

p3 : CX12 • SWAP12 ≈ CX12 • SWAP12
p3 = refl

p4 : CX21 • CX12 ≈ CX21 • CX12
p4 = refl

p5 : CX12 • SWAP12 ≈ CX21 • CX12
p5 = trans (sym p3) (trans p2 p4)

p6 : CX21 • CX12 ≈ CX12 • SWAP12
p6 = sym p5

proved : CX21 • CX12 ≈ CX12 • SWAP12
proved = p6
