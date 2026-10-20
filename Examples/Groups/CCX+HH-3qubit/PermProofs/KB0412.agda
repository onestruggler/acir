{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0412 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX02 ; CX12 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0023 as B23
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0035 as B35
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0127 as B127

p0 : CX12 • CX01 • CX02 • X1 ≈ CX01 • CX12 • X1
p0 = by-assoc-and (under (ε) (X1) B127.proved) Eq.refl Eq.refl

p1 : CX12 • CX01 • CX02 • X1 ≈ CX12 • CX01 • X1 • CX02
p1 = by-assoc-and (under (CX12 • CX01) (ε) B23.proved) Eq.refl Eq.refl

p2 : CX01 • CX12 • X1 ≈ CX12 • CX01 • X1 • CX02
p2 = trans (sym p0) p1

p3 : CX01 • CX12 • X1 ≈ CX01 • CX12 • X1
p3 = refl

p4 : CX12 • CX01 • X1 • CX02 ≈ CX12 • X1 • CX01 • CX02
p4 = by-assoc-and (under (CX12) (CX02) B35.proved) Eq.refl Eq.refl

p5 : CX12 • CX01 • X1 • CX02 ≈ CX12 • X1 • CX01 • CX02
p5 = trans p4 (refl)

p6 : CX01 • CX12 • X1 ≈ CX12 • X1 • CX01 • CX02
p6 = trans (sym p3) (trans p2 p5)

p7 : CX12 • X1 • CX01 • CX02 ≈ CX01 • CX12 • X1
p7 = sym p6

proved : CX12 • X1 • CX01 • CX02 ≈ CX01 • CX12 • X1
proved = p7
