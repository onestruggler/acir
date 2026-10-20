{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Proofs.KB0053 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX10 ; K01 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Proofs.KB0004 as B4
import Examples.Groups.CCX+HH-3qubit.Proofs.KB0052 as B52

p0 : CX10 • CX10 • K01 • K01 ≈ K01 • K01
p0 = by-assoc-and (under (ε) (K01) B52.proved) Eq.refl Eq.refl

p1 : CX10 • CX10 • K01 • K01 ≈ CX10 • CX10
p1 = by-assoc-and (under (CX10 • CX10) (ε) B4.proved) Eq.refl Eq.refl

p2 : K01 • K01 ≈ CX10 • CX10
p2 = trans (sym p0) p1

p3 : K01 • K01 ≈ ε
p3 = by-assoc-and (under (ε) (ε) B4.proved) Eq.refl Eq.refl

p4 : K01 • K01 ≈ ε
p4 = trans p3 (refl)

p5 : CX10 • CX10 ≈ CX10 • CX10
p5 = refl

p6 : ε ≈ CX10 • CX10
p6 = trans (sym p4) (trans p2 p5)

p7 : CX10 • CX10 ≈ ε
p7 = sym p6

proved : CX10 • CX10 ≈ ε
proved = p7
