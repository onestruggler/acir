{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0910 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX12 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0144 as B144
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0190 as B190
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0221 as B221

p0 : CX01 • X0 • X1 • CX12 • X1 ≈ X0 • CX01 • CX12 • X1
p0 = by-assoc-and (under (ε) (CX12 • X1) B190.proved) Eq.refl Eq.refl

p1 : CX01 • X0 • X1 • CX12 • X1 ≈ CX01 • X0 • X2 • CX12
p1 = by-assoc-and (under (CX01 • X0) (ε) B144.proved) Eq.refl Eq.refl

p2 : X0 • CX01 • CX12 • X1 ≈ CX01 • X0 • X2 • CX12
p2 = trans (sym p0) p1

p3 : X0 • CX01 • CX12 • X1 ≈ X0 • CX01 • CX12 • X1
p3 = refl

p4 : CX01 • X0 • X2 • CX12 ≈ X2 • CX01 • X0 • CX12
p4 = by-assoc-and (under (ε) (CX12) B221.proved) Eq.refl Eq.refl

p5 : CX01 • X0 • X2 • CX12 ≈ X2 • CX01 • X0 • CX12
p5 = trans p4 (refl)

p6 : X0 • CX01 • CX12 • X1 ≈ X2 • CX01 • X0 • CX12
p6 = trans (sym p3) (trans p2 p5)

p7 : X2 • CX01 • X0 • CX12 ≈ X0 • CX01 • CX12 • X1
p7 = sym p6

proved : X2 • CX01 • X0 • CX12 ≈ X0 • CX01 • CX12 • X1
proved = p7
