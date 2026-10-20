{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB2829 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CX01 ; CX02 ; CX12 ; CX21 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0472 as B472
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0962 as B962
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1431 as B1431
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1448 as B1448

p0 : X1 • CCX02 • CCX01 • X1 • CCX02 ≈ X1 • CX12 • CCX02 • CX12 • X1
p0 = by-assoc-and (under (X1) (ε) B962.proved) Eq.refl Eq.refl

p1 : X1 • CCX02 • CCX01 • X1 • CCX02 ≈ CCX02 • CX02 • CCX01 • CCX02
p1 = by-assoc-and (under (ε) (CCX02) B472.proved) Eq.refl Eq.refl

p2 : X1 • CX12 • CCX02 • CX12 • X1 ≈ CCX02 • CX02 • CCX01 • CCX02
p2 = trans (sym p0) p1

p3 : X1 • CX12 • CCX02 • CX12 • X1 ≈ X1 • CX12 • CCX02 • CX12 • X1
p3 = refl

p4 : CCX02 • CX02 • CCX01 • CCX02 ≈ CX21 • CX02 • CCX01 • CX21
p4 = by-assoc-and (under (ε) (ε) B1431.proved) Eq.refl Eq.refl

p5 : CX21 • CX02 • CCX01 • CX21 ≈ CX12 • CX01 • CCX02 • CX12
p5 = by-assoc-and (under (ε) (ε) B1448.proved) Eq.refl Eq.refl

p6 : CCX02 • CX02 • CCX01 • CCX02 ≈ CX12 • CX01 • CCX02 • CX12
p6 = trans p4 (trans p5 (refl))

p7 : X1 • CX12 • CCX02 • CX12 • X1 ≈ CX12 • CX01 • CCX02 • CX12
p7 = trans (sym p3) (trans p2 p6)

proved : X1 • CX12 • CCX02 • CX12 • X1 ≈ CX12 • CX01 • CCX02 • CX12
proved = p7
