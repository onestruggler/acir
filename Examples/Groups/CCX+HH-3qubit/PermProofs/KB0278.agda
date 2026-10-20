{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0278 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CX12 ; CX21 ; SWAP12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0031 as B31
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0061 as B61
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0107 as B107
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0226 as B226

p0 : SWAP12 • CCX01 • CX12 ≈ CCX02 • SWAP12 • CX12
p0 = by-assoc-and (under (ε) (CX12) B107.proved) Eq.refl Eq.refl

p1 : SWAP12 • CCX01 • CX12 ≈ SWAP12 • CX12 • CCX01
p1 = by-assoc-and (under (SWAP12) (ε) B31.proved) Eq.refl Eq.refl

p2 : CCX02 • SWAP12 • CX12 ≈ SWAP12 • CX12 • CCX01
p2 = trans (sym p0) p1

p3 : CCX02 • SWAP12 • CX12 ≈ CCX02 • CX12 • CX21
p3 = by-assoc-and (under (CCX02) (ε) B61.proved) Eq.refl Eq.refl

p4 : CCX02 • CX12 • CX21 ≈ CX21 • CCX02 • SWAP12
p4 = by-assoc-and (under (ε) (ε) B226.proved) Eq.refl Eq.refl

p5 : CCX02 • SWAP12 • CX12 ≈ CX21 • CCX02 • SWAP12
p5 = trans p3 (trans p4 (refl))

p6 : SWAP12 • CX12 • CCX01 ≈ CX12 • CX21 • CCX01
p6 = by-assoc-and (under (ε) (CCX01) B61.proved) Eq.refl Eq.refl

p7 : SWAP12 • CX12 • CCX01 ≈ CX12 • CX21 • CCX01
p7 = trans p6 (refl)

p8 : CX21 • CCX02 • SWAP12 ≈ CX12 • CX21 • CCX01
p8 = trans (sym p5) (trans p2 p7)

proved : CX21 • CCX02 • SWAP12 ≈ CX12 • CX21 • CCX01
proved = p8
