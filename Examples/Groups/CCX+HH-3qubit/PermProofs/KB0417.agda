{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0417 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CX12 ; CX21 ; SWAP12 ; X0 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0020 as B20
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 as B45
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0060 as B60
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0061 as B61
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0129 as B129

p0 : SWAP12 • CX12 • CX21 • CCX02 • X0 ≈ SWAP12 • CX12 • X0 • CCX02
p0 = by-assoc-and (under (SWAP12 • CX12) (ε) B129.proved) Eq.refl Eq.refl

p1 : SWAP12 • CX12 • CX21 • CCX02 • X0 ≈ CX12 • CCX02 • X0
p1 = by-assoc-and (under (ε) (CCX02 • X0) B60.proved) Eq.refl Eq.refl

p2 : SWAP12 • CX12 • X0 • CCX02 ≈ CX12 • CCX02 • X0
p2 = trans (sym p0) p1

p3 : SWAP12 • CX12 • X0 • CCX02 ≈ CX12 • CX21 • X0 • CCX02
p3 = by-assoc-and (under (ε) (X0 • CCX02) B61.proved) Eq.refl Eq.refl

p4 : CX12 • CX21 • X0 • CCX02 ≈ CX12 • X0 • CX21 • CCX02
p4 = by-assoc-and (under (CX12) (CCX02) B20.proved) Eq.refl Eq.refl

p5 : CX12 • X0 • CX21 • CCX02 ≈ X0 • CX12 • CX21 • CCX02
p5 = by-assoc-and (under (ε) (CX21 • CCX02) B45.proved) Eq.refl Eq.refl

p6 : SWAP12 • CX12 • X0 • CCX02 ≈ X0 • CX12 • CX21 • CCX02
p6 = trans p3 (trans p4 (trans p5 (refl)))

p7 : CX12 • CCX02 • X0 ≈ CX12 • CCX02 • X0
p7 = refl

p8 : X0 • CX12 • CX21 • CCX02 ≈ CX12 • CCX02 • X0
p8 = trans (sym p6) (trans p2 p7)

proved : X0 • CX12 • CX21 • CCX02 ≈ CX12 • CCX02 • X0
proved = p8
