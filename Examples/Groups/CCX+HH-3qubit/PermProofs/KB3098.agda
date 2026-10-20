{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB3098 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX12 ; CX01 ; CX02 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0023 as B23
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0025 as B25
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0211 as B211
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0282 as B282

p0 : CCX01 • CCX12 • CCX01 • X1 • CX01 ≈ CCX01 • CCX12 • X1 • CX01 • CCX01
p0 = by-assoc-and (under (CCX01 • CCX12) (ε) B282.proved) Eq.refl Eq.refl

p1 : CCX01 • CCX12 • CCX01 • X1 • CX01 ≈ CX02 • CCX12 • CX02 • X1 • CX01
p1 = by-assoc-and (under (ε) (X1 • CX01) B211.proved) Eq.refl Eq.refl

p2 : CCX01 • CCX12 • X1 • CX01 • CCX01 ≈ CX02 • CCX12 • CX02 • X1 • CX01
p2 = trans (sym p0) p1

p3 : CCX01 • CCX12 • X1 • CX01 • CCX01 ≈ CCX01 • CCX12 • X1 • CX01 • CCX01
p3 = refl

p4 : CX02 • CCX12 • CX02 • X1 • CX01 ≈ CX02 • CCX12 • X1 • CX02 • CX01
p4 = by-assoc-and (under (CX02 • CCX12) (CX01) B23.proved) Eq.refl Eq.refl

p5 : CX02 • CCX12 • X1 • CX02 • CX01 ≈ CX02 • CCX12 • X1 • CX01 • CX02
p5 = by-assoc-and (under (CX02 • CCX12 • X1) (ε) B25.proved) Eq.refl Eq.refl

p6 : CX02 • CCX12 • CX02 • X1 • CX01 ≈ CX02 • CCX12 • X1 • CX01 • CX02
p6 = trans p4 (trans p5 (refl))

p7 : CCX01 • CCX12 • X1 • CX01 • CCX01 ≈ CX02 • CCX12 • X1 • CX01 • CX02
p7 = trans (sym p3) (trans p2 p6)

proved : CCX01 • CCX12 • X1 • CX01 • CCX01 ≈ CX02 • CCX12 • X1 • CX01 • CX02
proved = p7
