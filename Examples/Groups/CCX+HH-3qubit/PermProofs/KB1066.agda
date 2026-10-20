{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1066 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CX12 ; CX21 ; SWAP01 ; SWAP02 ; SWAP12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0049 as B49
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0053 as B53
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0253 as B253

p0 : CCX02 • CX12 • SWAP12 • SWAP02 ≈ CX21 • CCX02 • CX12 • SWAP02
p0 = by-assoc-and (under (ε) (SWAP02) B253.proved) Eq.refl Eq.refl

p1 : CCX02 • CX12 • SWAP12 • SWAP02 ≈ CCX02 • CX12 • SWAP02 • SWAP01
p1 = by-assoc-and (under (CCX02 • CX12) (ε) B49.proved) Eq.refl Eq.refl

p2 : CX21 • CCX02 • CX12 • SWAP02 ≈ CCX02 • CX12 • SWAP02 • SWAP01
p2 = trans (sym p0) p1

p3 : CX21 • CCX02 • CX12 • SWAP02 ≈ CX21 • CCX02 • CX12 • SWAP02
p3 = refl

p4 : CCX02 • CX12 • SWAP02 • SWAP01 ≈ CCX02 • CX12 • SWAP01 • SWAP12
p4 = by-assoc-and (under (CCX02 • CX12) (ε) B53.proved) Eq.refl Eq.refl

p5 : CCX02 • CX12 • SWAP02 • SWAP01 ≈ CCX02 • CX12 • SWAP01 • SWAP12
p5 = trans p4 (refl)

p6 : CX21 • CCX02 • CX12 • SWAP02 ≈ CCX02 • CX12 • SWAP01 • SWAP12
p6 = trans (sym p3) (trans p2 p5)

p7 : CCX02 • CX12 • SWAP01 • SWAP12 ≈ CX21 • CCX02 • CX12 • SWAP02
p7 = sym p6

proved : CCX02 • CX12 • SWAP01 • SWAP12 ≈ CX21 • CCX02 • CX12 • SWAP02
proved = p7
