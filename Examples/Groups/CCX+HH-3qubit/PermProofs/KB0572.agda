{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0572 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX12 ; CX02 ; CX20 ; SWAP02 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0017 as B17
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0086 as B86
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0104 as B104
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0203 as B203

p0 : SWAP02 • CCX01 • X1 • CX02 ≈ SWAP02 • X1 • CCX01
p0 = by-assoc-and (under (SWAP02) (ε) B203.proved) Eq.refl Eq.refl

p1 : SWAP02 • CCX01 • X1 • CX02 ≈ CCX12 • SWAP02 • X1 • CX02
p1 = by-assoc-and (under (ε) (X1 • CX02) B104.proved) Eq.refl Eq.refl

p2 : SWAP02 • X1 • CCX01 ≈ CCX12 • SWAP02 • X1 • CX02
p2 = trans (sym p0) p1

p3 : SWAP02 • X1 • CCX01 ≈ X1 • SWAP02 • CCX01
p3 = by-assoc-and (under (ε) (CCX01) B17.proved) Eq.refl Eq.refl

p4 : X1 • SWAP02 • CCX01 ≈ X1 • CCX12 • SWAP02
p4 = by-assoc-and (under (X1) (ε) B104.proved) Eq.refl Eq.refl

p5 : SWAP02 • X1 • CCX01 ≈ X1 • CCX12 • SWAP02
p5 = trans p3 (trans p4 (refl))

p6 : CCX12 • SWAP02 • X1 • CX02 ≈ CCX12 • X1 • SWAP02 • CX02
p6 = by-assoc-and (under (CCX12) (CX02) B17.proved) Eq.refl Eq.refl

p7 : CCX12 • X1 • SWAP02 • CX02 ≈ CCX12 • X1 • CX02 • CX20
p7 = by-assoc-and (under (CCX12 • X1) (ε) B86.proved) Eq.refl Eq.refl

p8 : CCX12 • SWAP02 • X1 • CX02 ≈ CCX12 • X1 • CX02 • CX20
p8 = trans p6 (trans p7 (refl))

p9 : X1 • CCX12 • SWAP02 ≈ CCX12 • X1 • CX02 • CX20
p9 = trans (sym p5) (trans p2 p8)

p10 : CCX12 • X1 • CX02 • CX20 ≈ X1 • CCX12 • SWAP02
p10 = sym p9

proved : CCX12 • X1 • CX02 • CX20 ≈ X1 • CCX12 • SWAP02
proved = p10
