{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0962 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CX12 ; CX21 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0028 as B28
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0213 as B213
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0217 as B217

p0 : CCX02 • CCX01 • CCX02 • X1 ≈ CX21 • CCX01 • CX21 • X1
p0 = by-assoc-and (under (ε) (X1) B213.proved) Eq.refl Eq.refl

p1 : CCX02 • CCX01 • CCX02 • X1 ≈ CCX02 • CCX01 • X1 • CCX02
p1 = by-assoc-and (under (CCX02 • CCX01) (ε) B28.proved) Eq.refl Eq.refl

p2 : CX21 • CCX01 • CX21 • X1 ≈ CCX02 • CCX01 • X1 • CCX02
p2 = trans (sym p0) p1

p3 : CX21 • CCX01 • CX21 • X1 ≈ CX12 • CCX02 • CX12 • X1
p3 = by-assoc-and (under (ε) (X1) B217.proved) Eq.refl Eq.refl

p4 : CX21 • CCX01 • CX21 • X1 ≈ CX12 • CCX02 • CX12 • X1
p4 = trans p3 (refl)

p5 : CCX02 • CCX01 • X1 • CCX02 ≈ CCX02 • CCX01 • X1 • CCX02
p5 = refl

p6 : CX12 • CCX02 • CX12 • X1 ≈ CCX02 • CCX01 • X1 • CCX02
p6 = trans (sym p4) (trans p2 p5)

p7 : CCX02 • CCX01 • X1 • CCX02 ≈ CX12 • CCX02 • CX12 • X1
p7 = sym p6

proved : CCX02 • CCX01 • X1 • CCX02 ≈ CX12 • CCX02 • CX12 • X1
proved = p7
