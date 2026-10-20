{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1173 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX12 ; CX12 ; CX21 ; SWAP12 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0055 as B55
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0061 as B61
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0078 as B78
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0287 as B287

p0 : SWAP12 • CCX12 • X2 • CX12 ≈ SWAP12 • X2 • CX12 • CCX12
p0 = by-assoc-and (under (SWAP12) (ε) B287.proved) Eq.refl Eq.refl

p1 : SWAP12 • CCX12 • X2 • CX12 ≈ CCX12 • SWAP12 • X2 • CX12
p1 = by-assoc-and (under (ε) (X2 • CX12) B78.proved) Eq.refl Eq.refl

p2 : SWAP12 • X2 • CX12 • CCX12 ≈ CCX12 • SWAP12 • X2 • CX12
p2 = trans (sym p0) p1

p3 : SWAP12 • X2 • CX12 • CCX12 ≈ X1 • SWAP12 • CX12 • CCX12
p3 = by-assoc-and (under (ε) (CX12 • CCX12) B55.proved) Eq.refl Eq.refl

p4 : X1 • SWAP12 • CX12 • CCX12 ≈ X1 • CX12 • CX21 • CCX12
p4 = by-assoc-and (under (X1) (CCX12) B61.proved) Eq.refl Eq.refl

p5 : SWAP12 • X2 • CX12 • CCX12 ≈ X1 • CX12 • CX21 • CCX12
p5 = trans p3 (trans p4 (refl))

p6 : CCX12 • SWAP12 • X2 • CX12 ≈ CCX12 • X1 • SWAP12 • CX12
p6 = by-assoc-and (under (CCX12) (CX12) B55.proved) Eq.refl Eq.refl

p7 : CCX12 • X1 • SWAP12 • CX12 ≈ CCX12 • X1 • CX12 • CX21
p7 = by-assoc-and (under (CCX12 • X1) (ε) B61.proved) Eq.refl Eq.refl

p8 : CCX12 • SWAP12 • X2 • CX12 ≈ CCX12 • X1 • CX12 • CX21
p8 = trans p6 (trans p7 (refl))

p9 : X1 • CX12 • CX21 • CCX12 ≈ CCX12 • X1 • CX12 • CX21
p9 = trans (sym p5) (trans p2 p8)

p10 : CCX12 • X1 • CX12 • CX21 ≈ X1 • CX12 • CX21 • CCX12
p10 = sym p9

proved : CCX12 • X1 • CX12 • CX21 ≈ X1 • CX12 • CX21 • CCX12
proved = p10
