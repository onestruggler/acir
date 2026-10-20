{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0234 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX12 ; CX21 ; SWAP12 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0034 as B34
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0041 as B41
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0055 as B55

p0 : CX21 • SWAP12 • X2 ≈ CX21 • X1 • SWAP12
p0 = by-assoc-and (under (CX21) (ε) B55.proved) Eq.refl Eq.refl

p1 : CX21 • SWAP12 • X2 ≈ CX12 • CX21 • X2
p1 = by-assoc-and (under (ε) (X2) B41.proved) Eq.refl Eq.refl

p2 : CX21 • X1 • SWAP12 ≈ CX12 • CX21 • X2
p2 = trans (sym p0) p1

p3 : CX21 • X1 • SWAP12 ≈ X1 • CX21 • SWAP12
p3 = by-assoc-and (under (ε) (SWAP12) B34.proved) Eq.refl Eq.refl

p4 : X1 • CX21 • SWAP12 ≈ X1 • CX12 • CX21
p4 = by-assoc-and (under (X1) (ε) B41.proved) Eq.refl Eq.refl

p5 : CX21 • X1 • SWAP12 ≈ X1 • CX12 • CX21
p5 = trans p3 (trans p4 (refl))

p6 : CX12 • CX21 • X2 ≈ CX12 • CX21 • X2
p6 = refl

p7 : X1 • CX12 • CX21 ≈ CX12 • CX21 • X2
p7 = trans (sym p5) (trans p2 p6)

p8 : CX12 • CX21 • X2 ≈ X1 • CX12 • CX21
p8 = sym p7

proved : CX12 • CX21 • X2 ≈ X1 • CX12 • CX21
proved = p8
