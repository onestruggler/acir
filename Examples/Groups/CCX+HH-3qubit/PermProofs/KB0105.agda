{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0105 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX12 ; SWAP02 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0002 as B2
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0103 as B103

p0 : SWAP02 • CCX12 • SWAP02 • SWAP02 ≈ CCX01 • SWAP02
p0 = by-assoc-and (under (ε) (SWAP02) B103.proved) Eq.refl Eq.refl

p1 : SWAP02 • CCX12 • SWAP02 • SWAP02 ≈ SWAP02 • CCX12
p1 = by-assoc-and (under (SWAP02 • CCX12) (ε) B2.proved) Eq.refl Eq.refl

p2 : CCX01 • SWAP02 ≈ SWAP02 • CCX12
p2 = trans (sym p0) p1

p3 : CCX01 • SWAP02 ≈ CCX01 • SWAP02
p3 = refl

p4 : SWAP02 • CCX12 ≈ SWAP02 • CCX12
p4 = refl

p5 : CCX01 • SWAP02 ≈ SWAP02 • CCX12
p5 = trans (sym p3) (trans p2 p4)

p6 : SWAP02 • CCX12 ≈ CCX01 • SWAP02
p6 = sym p5

proved : SWAP02 • CCX12 ≈ CCX01 • SWAP02
proved = p6
