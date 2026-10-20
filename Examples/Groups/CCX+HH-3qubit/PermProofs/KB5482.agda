{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB5482 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX21 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0007 as B7
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0039 as B39
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0328 as B328
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB2914 as B2914

p0 : CX21 • CCX02 • CCX01 • CX21 • CCX12 • CCX01 • CCX02 ≈ CX21 • CCX02 • CX21 • CCX12 • CCX01
p0 = by-assoc-and (under (CX21 • CCX02) (ε) B2914.proved) Eq.refl Eq.refl

p1 : CX21 • CCX02 • CCX01 • CX21 • CCX12 • CCX01 • CCX02 ≈ CCX01 • CCX02 • CCX12 • CCX01 • CCX02
p1 = by-assoc-and (under (ε) (CCX12 • CCX01 • CCX02) B328.proved) Eq.refl Eq.refl

p2 : CX21 • CCX02 • CX21 • CCX12 • CCX01 ≈ CCX01 • CCX02 • CCX12 • CCX01 • CCX02
p2 = trans (sym p0) p1

p3 : CX21 • CCX02 • CX21 • CCX12 • CCX01 ≈ CX21 • CX21 • CCX02 • CCX12 • CCX01
p3 = by-assoc-and (under (CX21) (CCX12 • CCX01) B39.proved) Eq.refl Eq.refl

p4 : CX21 • CX21 • CCX02 • CCX12 • CCX01 ≈ CCX02 • CCX12 • CCX01
p4 = by-assoc-and (under (ε) (CCX02 • CCX12 • CCX01) B7.proved) Eq.refl Eq.refl

p5 : CX21 • CCX02 • CX21 • CCX12 • CCX01 ≈ CCX02 • CCX12 • CCX01
p5 = trans p3 (trans p4 (refl))

p6 : CCX01 • CCX02 • CCX12 • CCX01 • CCX02 ≈ CCX01 • CCX02 • CCX12 • CCX01 • CCX02
p6 = refl

p7 : CCX02 • CCX12 • CCX01 ≈ CCX01 • CCX02 • CCX12 • CCX01 • CCX02
p7 = trans (sym p5) (trans p2 p6)

p8 : CCX01 • CCX02 • CCX12 • CCX01 • CCX02 ≈ CCX02 • CCX12 • CCX01
p8 = sym p7

proved : CCX01 • CCX02 • CCX12 • CCX01 • CCX02 ≈ CCX02 • CCX12 • CCX01
proved = p8
