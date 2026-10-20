{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0164 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX02 ; CX12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0008 as B8
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0027 as B27
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0127 as B127

p0 : CX12 • CX01 • CX02 • CX02 ≈ CX01 • CX12 • CX02
p0 = by-assoc-and (under (ε) (CX02) B127.proved) Eq.refl Eq.refl

p1 : CX12 • CX01 • CX02 • CX02 ≈ CX12 • CX01
p1 = by-assoc-and (under (CX12 • CX01) (ε) B8.proved) Eq.refl Eq.refl

p2 : CX01 • CX12 • CX02 ≈ CX12 • CX01
p2 = trans (sym p0) p1

p3 : CX01 • CX12 • CX02 ≈ CX01 • CX02 • CX12
p3 = by-assoc-and (under (CX01) (ε) B27.proved) Eq.refl Eq.refl

p4 : CX01 • CX12 • CX02 ≈ CX01 • CX02 • CX12
p4 = trans p3 (refl)

p5 : CX12 • CX01 ≈ CX12 • CX01
p5 = refl

p6 : CX01 • CX02 • CX12 ≈ CX12 • CX01
p6 = trans (sym p4) (trans p2 p5)

proved : CX01 • CX02 • CX12 ≈ CX12 • CX01
proved = p6
