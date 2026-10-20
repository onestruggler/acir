{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0061 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX12 ; CX21 ; SWAP12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0001 as B1
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0060 as B60

p0 : SWAP12 • SWAP12 • CX12 • CX21 ≈ SWAP12 • CX12
p0 = by-assoc-and (under (SWAP12) (ε) B60.proved) Eq.refl Eq.refl

p1 : SWAP12 • SWAP12 • CX12 • CX21 ≈ CX12 • CX21
p1 = by-assoc-and (under (ε) (CX12 • CX21) B1.proved) Eq.refl Eq.refl

p2 : SWAP12 • CX12 ≈ CX12 • CX21
p2 = trans (sym p0) p1

p3 : SWAP12 • CX12 ≈ SWAP12 • CX12
p3 = refl

p4 : CX12 • CX21 ≈ CX12 • CX21
p4 = refl

p5 : SWAP12 • CX12 ≈ CX12 • CX21
p5 = trans (sym p3) (trans p2 p4)

proved : SWAP12 • CX12 ≈ CX12 • CX21
proved = p5
