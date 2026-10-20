{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB2850 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX01 ; CX10 ; CX12 ; CX20 ; CX21 ; SWAP02 ; SWAP12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0202 as B202
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1029 as B1029

p0 : CCX01 • CX10 • CX12 • CX21 • SWAP02 ≈ CCX01 • CX01 • CX10 • CX20 • SWAP12
p0 = by-assoc-and (under (CCX01) (ε) B1029.proved) Eq.refl Eq.refl

p1 : CCX01 • CX10 • CX12 • CX21 • SWAP02 ≈ CX10 • CCX01 • CX21 • SWAP02
p1 = by-assoc-and (under (ε) (CX21 • SWAP02) B202.proved) Eq.refl Eq.refl

p2 : CCX01 • CX01 • CX10 • CX20 • SWAP12 ≈ CX10 • CCX01 • CX21 • SWAP02
p2 = trans (sym p0) p1

p3 : CCX01 • CX01 • CX10 • CX20 • SWAP12 ≈ CCX01 • CX01 • CX10 • CX20 • SWAP12
p3 = refl

p4 : CX10 • CCX01 • CX21 • SWAP02 ≈ CX10 • CCX01 • CX21 • SWAP02
p4 = refl

p5 : CCX01 • CX01 • CX10 • CX20 • SWAP12 ≈ CX10 • CCX01 • CX21 • SWAP02
p5 = trans (sym p3) (trans p2 p4)

proved : CCX01 • CX01 • CX10 • CX20 • SWAP12 ≈ CX10 • CCX01 • CX21 • SWAP02
proved = p5
