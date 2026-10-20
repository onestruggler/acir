{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0884 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX12 ; CX10 ; CX12 ; X0 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 as B45
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0046 as B46
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0140 as B140
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0181 as B181

p0 : CX12 • CCX12 • CX12 • CCX01 • X0 ≈ CX10 • CCX12 • CCX01 • X0
p0 = by-assoc-and (under (ε) (CCX01 • X0) B181.proved) Eq.refl Eq.refl

p1 : CX12 • CCX12 • CX12 • CCX01 • X0 ≈ CX12 • CCX12 • X0 • CCX01
p1 = by-assoc-and (under (CX12 • CCX12) (ε) B140.proved) Eq.refl Eq.refl

p2 : CX10 • CCX12 • CCX01 • X0 ≈ CX12 • CCX12 • X0 • CCX01
p2 = trans (sym p0) p1

p3 : CX10 • CCX12 • CCX01 • X0 ≈ CX10 • CCX12 • CCX01 • X0
p3 = refl

p4 : CX12 • CCX12 • X0 • CCX01 ≈ CX12 • X0 • CCX12 • CCX01
p4 = by-assoc-and (under (CX12) (CCX01) B46.proved) Eq.refl Eq.refl

p5 : CX12 • X0 • CCX12 • CCX01 ≈ X0 • CX12 • CCX12 • CCX01
p5 = by-assoc-and (under (ε) (CCX12 • CCX01) B45.proved) Eq.refl Eq.refl

p6 : CX12 • CCX12 • X0 • CCX01 ≈ X0 • CX12 • CCX12 • CCX01
p6 = trans p4 (trans p5 (refl))

p7 : CX10 • CCX12 • CCX01 • X0 ≈ X0 • CX12 • CCX12 • CCX01
p7 = trans (sym p3) (trans p2 p6)

proved : CX10 • CCX12 • CCX01 • X0 ≈ X0 • CX12 • CCX12 • CCX01
proved = p7
