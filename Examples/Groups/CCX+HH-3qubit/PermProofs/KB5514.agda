{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB5514 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX02 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0025 as B25
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0706 as B706
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB3165 as B3165

p0 : CCX01 • CX01 • CCX12 • CCX01 • CX01 • CCX12 ≈ CCX01 • CCX12 • CCX02 • CX02 • CCX01
p0 = by-assoc-and (under (CCX01) (ε) B3165.proved) Eq.refl Eq.refl

p1 : CCX01 • CX01 • CCX12 • CCX01 • CX01 • CCX12 ≈ CX01 • CCX12 • CX02 • CX01 • CCX12
p1 = by-assoc-and (under (ε) (CX01 • CCX12) B706.proved) Eq.refl Eq.refl

p2 : CCX01 • CCX12 • CCX02 • CX02 • CCX01 ≈ CX01 • CCX12 • CX02 • CX01 • CCX12
p2 = trans (sym p0) p1

p3 : CCX01 • CCX12 • CCX02 • CX02 • CCX01 ≈ CCX01 • CCX12 • CCX02 • CX02 • CCX01
p3 = refl

p4 : CX01 • CCX12 • CX02 • CX01 • CCX12 ≈ CX01 • CCX12 • CX01 • CX02 • CCX12
p4 = by-assoc-and (under (CX01 • CCX12) (CCX12) B25.proved) Eq.refl Eq.refl

p5 : CX01 • CCX12 • CX02 • CX01 • CCX12 ≈ CX01 • CCX12 • CX01 • CX02 • CCX12
p5 = trans p4 (refl)

p6 : CCX01 • CCX12 • CCX02 • CX02 • CCX01 ≈ CX01 • CCX12 • CX01 • CX02 • CCX12
p6 = trans (sym p3) (trans p2 p5)

proved : CCX01 • CCX12 • CCX02 • CX02 • CCX01 ≈ CX01 • CCX12 • CX01 • CX02 • CCX12
proved = p6
