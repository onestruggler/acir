{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.comm14 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CX02 ; CX12 ; CX21 ; SWAP12 ; X0 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0012 as B12
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0027 as B27
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 as B45
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0079 as B79
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0107 as B107
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0108 as B108
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0150 as B150
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0152 as B152
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0214 as B214
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0308 as B308
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0407 as B407
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0515 as B515
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1329 as B1329

p0 : X0 • CCX01 • CCX02 • CCX01 • X0 • X1 • CCX01 • X1 ≈ X0 • CX12 • CCX02 • CX12 • X0 • X1 • CCX01 • X1
p0 = by-assoc-and (under (X0) (X0 • X1 • CCX01 • X1) B214.proved) Eq.refl Eq.refl

p1 : X0 • CX12 • CCX02 • CX12 • X0 • X1 • CCX01 • X1 ≈ X0 • CX12 • CCX02 • X0 • CX12 • X1 • CCX01 • X1
p1 = by-assoc-and (under (X0 • CX12 • CCX02) (X1 • CCX01 • X1) B45.proved) Eq.refl Eq.refl

p2 : X0 • CX12 • CCX02 • X0 • CX12 • X1 • CCX01 • X1 ≈ CX12 • CX21 • CCX02 • CX12 • X1 • CCX01 • X1
p2 = by-assoc-and (under (ε) (CX12 • X1 • CCX01 • X1) B515.proved) Eq.refl Eq.refl

p3 : CX12 • CX21 • CCX02 • CX12 • X1 • CCX01 • X1 ≈ CX12 • CX21 • CCX02 • CX12 • CX02 • CCX01
p3 = by-assoc-and (under (CX12 • CX21 • CCX02 • CX12) (ε) B150.proved) Eq.refl Eq.refl

p4 : CX12 • CX21 • CCX02 • CX12 • CX02 • CCX01 ≈ CX12 • CX21 • CCX02 • CX02 • CX12 • CCX01
p4 = by-assoc-and (under (CX12 • CX21 • CCX02) (CCX01) B27.proved) Eq.refl Eq.refl

p5 : CX12 • CX21 • CCX02 • CX02 • CX12 • CCX01 ≈ CX12 • CX02 • CX21 • CCX02 • CX12 • CCX01
p5 = by-assoc-and (under (CX12) (CX12 • CCX01) B407.proved) Eq.refl Eq.refl

p6 : CX12 • CX02 • CX21 • CCX02 • CX12 • CCX01 ≈ CX02 • CX12 • CX21 • CCX02 • CX12 • CCX01
p6 = by-assoc-and (under (ε) (CX21 • CCX02 • CX12 • CCX01) B27.proved) Eq.refl Eq.refl

p7 : CX02 • CX12 • CX21 • CCX02 • CX12 • CCX01 ≈ CX02 • CX12 • CX21 • CX12 • CCX01 • CCX02
p7 = by-assoc-and (under (CX02 • CX12 • CX21) (ε) B308.proved) Eq.refl Eq.refl

p8 : CX02 • CX12 • CX21 • CX12 • CCX01 • CCX02 ≈ CX02 • SWAP12 • CCX01 • CCX02
p8 = by-assoc-and (under (CX02) (CCX01 • CCX02) B79.proved) Eq.refl Eq.refl

p9 : CX02 • SWAP12 • CCX01 • CCX02 ≈ CX02 • CCX02 • SWAP12 • CCX02
p9 = by-assoc-and (under (CX02) (CCX02) B107.proved) Eq.refl Eq.refl

p10 : CX02 • CCX02 • SWAP12 • CCX02 ≈ CX02 • CCX02 • CCX01 • SWAP12
p10 = by-assoc-and (under (CX02 • CCX02) (ε) B108.proved) Eq.refl Eq.refl

p11 : X0 • CCX01 • CCX02 • CCX01 • X0 • X1 • CCX01 • X1 ≈ CX02 • CCX02 • CCX01 • SWAP12
p11 = trans p0 (trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (refl)))))))))))

p12 : X1 • CCX01 • X1 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X0
p12 = by-assoc-and (under (ε) (X0 • CCX01 • CCX02 • CCX01 • X0) B150.proved) Eq.refl Eq.refl

p13 : CX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX02 • X0 • CX12 • CCX02 • CCX01 • X0
p13 = by-assoc-and (under (CX02) (CCX02 • CCX01 • X0) B152.proved) Eq.refl Eq.refl

p14 : CX02 • X0 • CX12 • CCX02 • CCX01 • X0 ≈ CX02 • X0 • X0 • CCX02 • CCX01 • SWAP12
p14 = by-assoc-and (under (CX02 • X0) (ε) B1329.proved) Eq.refl Eq.refl

p15 : CX02 • X0 • X0 • CCX02 • CCX01 • SWAP12 ≈ CX02 • CCX02 • CCX01 • SWAP12
p15 = by-assoc-and (under (CX02) (CCX02 • CCX01 • SWAP12) B12.proved) Eq.refl Eq.refl

p16 : X1 • CCX01 • X1 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX02 • CCX02 • CCX01 • SWAP12
p16 = trans p12 (trans p13 (trans p14 (trans p15 (refl))))

proved : X0 • CCX01 • CCX02 • CCX01 • X0 • X1 • CCX01 • X1 ≈ X1 • CCX01 • X1 • X0 • CCX01 • CCX02 • CCX01 • X0
proved = trans p11 (sym p16)
