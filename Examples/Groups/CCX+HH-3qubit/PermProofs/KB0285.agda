{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0285 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CX01 ; CX02 ; CX12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0127 as B127
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0149 as B149

p0 : CX12 • CX01 • CX02 • CCX02 ≈ CX12 • CCX02 • CX02
p0 = by-assoc-and (under (CX12) (ε) B149.proved) Eq.refl Eq.refl

p1 : CX12 • CX01 • CX02 • CCX02 ≈ CX01 • CX12 • CCX02
p1 = by-assoc-and (under (ε) (CCX02) B127.proved) Eq.refl Eq.refl

p2 : CX12 • CCX02 • CX02 ≈ CX01 • CX12 • CCX02
p2 = trans (sym p0) p1

p3 : CX12 • CCX02 • CX02 ≈ CX12 • CCX02 • CX02
p3 = refl

p4 : CX01 • CX12 • CCX02 ≈ CX01 • CX12 • CCX02
p4 = refl

p5 : CX12 • CCX02 • CX02 ≈ CX01 • CX12 • CCX02
p5 = trans (sym p3) (trans p2 p4)

proved : CX12 • CCX02 • CX02 ≈ CX01 • CX12 • CCX02
proved = p5
