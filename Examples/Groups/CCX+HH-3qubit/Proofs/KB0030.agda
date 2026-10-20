{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Proofs.KB0030 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX10 ; SWAP01 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Proofs.KB0001 as B1
import Examples.Groups.CCX+HH-3qubit.Proofs.KB0029 as B29

p0 : CX01 • CX01 • CX10 • CX01 ≈ CX01 • SWAP01
p0 = by-assoc-and (under (CX01) (ε) B29.proved) Eq.refl Eq.refl

p1 : CX01 • CX01 • CX10 • CX01 ≈ CX10 • CX01
p1 = by-assoc-and (under (ε) (CX10 • CX01) B1.proved) Eq.refl Eq.refl

p2 : CX01 • SWAP01 ≈ CX10 • CX01
p2 = trans (sym p0) p1

p3 : CX01 • SWAP01 ≈ CX01 • SWAP01
p3 = refl

p4 : CX10 • CX01 ≈ CX10 • CX01
p4 = refl

p5 : CX01 • SWAP01 ≈ CX10 • CX01
p5 = trans (sym p3) (trans p2 p4)

p6 : CX10 • CX01 ≈ CX01 • SWAP01
p6 = sym p5

proved : CX10 • CX01 ≈ CX01 • SWAP01
proved = p6
