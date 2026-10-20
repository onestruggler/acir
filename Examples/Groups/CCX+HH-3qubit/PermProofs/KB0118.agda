{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0118 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX10 ; CX12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0031 as B31

import Examples.Groups.CCX+HH-3qubit.Tietze.drel90 as Tdrel90
p0 : CX10 • CCX01 ≈ CCX01 • CX12 • CX10
p0 = Tdrel90.proved

p1 : CX10 • CCX01 ≈ CX10 • CCX01
p1 = refl

p2 : CCX01 • CX12 • CX10 ≈ CX12 • CCX01 • CX10
p2 = by-assoc-and (under (ε) (CX10) B31.proved) Eq.refl Eq.refl

p3 : CCX01 • CX12 • CX10 ≈ CX12 • CCX01 • CX10
p3 = trans p2 (refl)

p4 : CX10 • CCX01 ≈ CX12 • CCX01 • CX10
p4 = trans (sym p1) (trans p0 p3)

p5 : CX12 • CCX01 • CX10 ≈ CX10 • CCX01
p5 = sym p4

proved : CX12 • CCX01 • CX10 ≈ CX10 • CCX01
proved = p5
