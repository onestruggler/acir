{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Proofs.KB0028 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX10 ; K01 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Proofs.KB0004 as B4
import Examples.Groups.CCX+HH-3qubit.Proofs.KB0026 as B26

p0 : K01 • CX01 • K01 • K01 ≈ CX10 • K01
p0 = by-assoc-and (under (ε) (K01) B26.proved) Eq.refl Eq.refl

p1 : K01 • CX01 • K01 • K01 ≈ K01 • CX01
p1 = by-assoc-and (under (K01 • CX01) (ε) B4.proved) Eq.refl Eq.refl

p2 : CX10 • K01 ≈ K01 • CX01
p2 = trans (sym p0) p1

p3 : CX10 • K01 ≈ CX10 • K01
p3 = refl

p4 : K01 • CX01 ≈ K01 • CX01
p4 = refl

p5 : CX10 • K01 ≈ K01 • CX01
p5 = trans (sym p3) (trans p2 p4)

p6 : K01 • CX01 ≈ CX10 • K01
p6 = sym p5

proved : K01 • CX01 ≈ CX10 • K01
proved = p6
