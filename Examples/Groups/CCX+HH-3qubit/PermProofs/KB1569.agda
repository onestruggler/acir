{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1569 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX02 ; CX20 ; CX21 ; SWAP02 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0177 as B177
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0271 as B271
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0276 as B276

p0 : CCX12 • CX02 • CX20 • CCX02 • CX20 ≈ CX20 • CCX12 • SWAP02 • CCX02 • CX20
p0 = by-assoc-and (under (ε) (CCX02 • CX20) B271.proved) Eq.refl Eq.refl

p1 : CCX12 • CX02 • CX20 • CCX02 • CX20 ≈ CCX12 • CX02 • CX21 • CCX02
p1 = by-assoc-and (under (CCX12 • CX02) (ε) B177.proved) Eq.refl Eq.refl

p2 : CX20 • CCX12 • SWAP02 • CCX02 • CX20 ≈ CCX12 • CX02 • CX21 • CCX02
p2 = trans (sym p0) p1

p3 : CX20 • CCX12 • SWAP02 • CCX02 • CX20 ≈ CX02 • CX20 • CCX01 • CCX02 • CX20
p3 = by-assoc-and (under (ε) (CCX02 • CX20) B276.proved) Eq.refl Eq.refl

p4 : CX20 • CCX12 • SWAP02 • CCX02 • CX20 ≈ CX02 • CX20 • CCX01 • CCX02 • CX20
p4 = trans p3 (refl)

p5 : CCX12 • CX02 • CX21 • CCX02 ≈ CCX12 • CX02 • CX21 • CCX02
p5 = refl

p6 : CX02 • CX20 • CCX01 • CCX02 • CX20 ≈ CCX12 • CX02 • CX21 • CCX02
p6 = trans (sym p4) (trans p2 p5)

proved : CX02 • CX20 • CCX01 • CCX02 • CX20 ≈ CCX12 • CX02 • CX21 • CCX02
proved = p6
