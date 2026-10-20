{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0271 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX12 ; CX02 ; CX20 ; SWAP02 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0040 as B40
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0099 as B99

p0 : CCX12 • CX20 • SWAP02 ≈ CCX12 • CX02 • CX20
p0 = by-assoc-and (under (CCX12) (ε) B99.proved) Eq.refl Eq.refl

p1 : CCX12 • CX20 • SWAP02 ≈ CX20 • CCX12 • SWAP02
p1 = by-assoc-and (under (ε) (SWAP02) B40.proved) Eq.refl Eq.refl

p2 : CCX12 • CX02 • CX20 ≈ CX20 • CCX12 • SWAP02
p2 = trans (sym p0) p1

p3 : CCX12 • CX02 • CX20 ≈ CCX12 • CX02 • CX20
p3 = refl

p4 : CX20 • CCX12 • SWAP02 ≈ CX20 • CCX12 • SWAP02
p4 = refl

p5 : CCX12 • CX02 • CX20 ≈ CX20 • CCX12 • SWAP02
p5 = trans (sym p3) (trans p2 p4)

proved : CCX12 • CX02 • CX20 ≈ CX20 • CCX12 • SWAP02
proved = p5
