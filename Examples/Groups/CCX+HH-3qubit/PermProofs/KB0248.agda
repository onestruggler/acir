{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0248 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX01 ; CX10 ; SWAP01 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0042 as B42
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0074 as B74

p0 : CX10 • SWAP01 • CCX01 ≈ CX10 • CCX01 • SWAP01
p0 = by-assoc-and (under (CX10) (ε) B74.proved) Eq.refl Eq.refl

p1 : CX10 • SWAP01 • CCX01 ≈ CX01 • CX10 • CCX01
p1 = by-assoc-and (under (ε) (CCX01) B42.proved) Eq.refl Eq.refl

p2 : CX10 • CCX01 • SWAP01 ≈ CX01 • CX10 • CCX01
p2 = trans (sym p0) p1

p3 : CX10 • CCX01 • SWAP01 ≈ CX10 • CCX01 • SWAP01
p3 = refl

p4 : CX01 • CX10 • CCX01 ≈ CX01 • CX10 • CCX01
p4 = refl

p5 : CX10 • CCX01 • SWAP01 ≈ CX01 • CX10 • CCX01
p5 = trans (sym p3) (trans p2 p4)

proved : CX10 • CCX01 • SWAP01 ≈ CX01 • CX10 • CCX01
proved = p5
