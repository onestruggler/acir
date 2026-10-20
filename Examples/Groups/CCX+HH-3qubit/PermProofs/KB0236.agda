{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0236 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX02 ; CX10 ; CX12 ; CX20 ; SWAP02 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0027 as B27
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0059 as B59
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0086 as B86

p0 : SWAP02 • CX12 • CX02 ≈ CX10 • SWAP02 • CX02
p0 = by-assoc-and (under (ε) (CX02) B59.proved) Eq.refl Eq.refl

p1 : SWAP02 • CX12 • CX02 ≈ SWAP02 • CX02 • CX12
p1 = by-assoc-and (under (SWAP02) (ε) B27.proved) Eq.refl Eq.refl

p2 : CX10 • SWAP02 • CX02 ≈ SWAP02 • CX02 • CX12
p2 = trans (sym p0) p1

p3 : CX10 • SWAP02 • CX02 ≈ CX10 • CX02 • CX20
p3 = by-assoc-and (under (CX10) (ε) B86.proved) Eq.refl Eq.refl

p4 : CX10 • SWAP02 • CX02 ≈ CX10 • CX02 • CX20
p4 = trans p3 (refl)

p5 : SWAP02 • CX02 • CX12 ≈ CX02 • CX20 • CX12
p5 = by-assoc-and (under (ε) (CX12) B86.proved) Eq.refl Eq.refl

p6 : SWAP02 • CX02 • CX12 ≈ CX02 • CX20 • CX12
p6 = trans p5 (refl)

p7 : CX10 • CX02 • CX20 ≈ CX02 • CX20 • CX12
p7 = trans (sym p4) (trans p2 p6)

proved : CX10 • CX02 • CX20 ≈ CX02 • CX20 • CX12
proved = p7
