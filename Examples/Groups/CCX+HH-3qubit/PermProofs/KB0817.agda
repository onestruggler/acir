{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0817 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX02 ; CX12 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0027 as B27
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0029 as B29
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0036 as B36
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0037 as B37
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0125 as B125
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0153 as B153
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0795 as B795

p0 : X0 • CCX01 • X0 • X2 • CX02 ≈ CX12 • CCX01 • X2 • CX02
p0 = by-assoc-and (under (ε) (X2 • CX02) B153.proved) Eq.refl Eq.refl

p1 : X0 • CCX01 • X0 • X2 • CX02 ≈ X0 • CCX01 • CX02 • X0
p1 = by-assoc-and (under (X0 • CCX01) (ε) B125.proved) Eq.refl Eq.refl

p2 : CX12 • CCX01 • X2 • CX02 ≈ X0 • CCX01 • CX02 • X0
p2 = trans (sym p0) p1

p3 : CX12 • CCX01 • X2 • CX02 ≈ CX12 • X2 • CCX01 • CX02
p3 = by-assoc-and (under (CX12) (CX02) B29.proved) Eq.refl Eq.refl

p4 : CX12 • X2 • CCX01 • CX02 ≈ X2 • CX12 • CCX01 • CX02
p4 = by-assoc-and (under (ε) (CCX01 • CX02) B36.proved) Eq.refl Eq.refl

p5 : X2 • CX12 • CCX01 • CX02 ≈ X2 • CX12 • CX02 • CCX01
p5 = by-assoc-and (under (X2 • CX12) (ε) B37.proved) Eq.refl Eq.refl

p6 : X2 • CX12 • CX02 • CCX01 ≈ X2 • CX02 • CX12 • CCX01
p6 = by-assoc-and (under (X2) (CCX01) B27.proved) Eq.refl Eq.refl

p7 : X2 • CX02 • CX12 • CCX01 ≈ X1 • CX12 • CCX01 • X1
p7 = by-assoc-and (under (ε) (ε) B795.proved) Eq.refl Eq.refl

p8 : CX12 • CCX01 • X2 • CX02 ≈ X1 • CX12 • CCX01 • X1
p8 = trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (refl)))))

p9 : X0 • CCX01 • CX02 • X0 ≈ X0 • CX02 • CCX01 • X0
p9 = by-assoc-and (under (X0) (X0) B37.proved) Eq.refl Eq.refl

p10 : X0 • CCX01 • CX02 • X0 ≈ X0 • CX02 • CCX01 • X0
p10 = trans p9 (refl)

p11 : X1 • CX12 • CCX01 • X1 ≈ X0 • CX02 • CCX01 • X0
p11 = trans (sym p8) (trans p2 p10)

proved : X1 • CX12 • CCX01 • X1 ≈ X0 • CX02 • CCX01 • X0
proved = p11
