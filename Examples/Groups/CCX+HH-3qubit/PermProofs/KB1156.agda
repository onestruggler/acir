{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1156 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX12 ; CX02 ; CX20 ; SWAP02 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0104 as B104
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0277 as B277
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0854 as B854

p0 : CX20 • CCX01 • SWAP02 • CCX01 ≈ CX02 • CX20 • CCX12 • CCX01
p0 = by-assoc-and (under (ε) (CCX01) B277.proved) Eq.refl Eq.refl

p1 : CX20 • CCX01 • SWAP02 • CCX01 ≈ CX20 • CCX01 • CCX12 • SWAP02
p1 = by-assoc-and (under (CX20 • CCX01) (ε) B104.proved) Eq.refl Eq.refl

p2 : CX02 • CX20 • CCX12 • CCX01 ≈ CX20 • CCX01 • CCX12 • SWAP02
p2 = trans (sym p0) p1

p3 : CX02 • CX20 • CCX12 • CCX01 ≈ X1 • CCX01 • CCX12 • X1
p3 = by-assoc-and (under (ε) (ε) B854.proved) Eq.refl Eq.refl

p4 : CX02 • CX20 • CCX12 • CCX01 ≈ X1 • CCX01 • CCX12 • X1
p4 = trans p3 (refl)

p5 : CX20 • CCX01 • CCX12 • SWAP02 ≈ CX20 • CCX01 • CCX12 • SWAP02
p5 = refl

p6 : X1 • CCX01 • CCX12 • X1 ≈ CX20 • CCX01 • CCX12 • SWAP02
p6 = trans (sym p4) (trans p2 p5)

p7 : CX20 • CCX01 • CCX12 • SWAP02 ≈ X1 • CCX01 • CCX12 • X1
p7 = sym p6

proved : CX20 • CCX01 • CCX12 • SWAP02 ≈ X1 • CCX01 • CCX12 • X1
proved = p7
