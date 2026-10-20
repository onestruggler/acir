{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1050 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX01 ; CX10 ; SWAP01 ; X0 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0042 as B42
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0096 as B96
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0248 as B248
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0366 as B366

p0 : CX10 • CCX01 • SWAP01 • X1 ≈ CX01 • CX10 • CCX01 • X1
p0 = by-assoc-and (under (ε) (X1) B248.proved) Eq.refl Eq.refl

p1 : CX10 • CCX01 • SWAP01 • X1 ≈ CX10 • CCX01 • X0 • SWAP01
p1 = by-assoc-and (under (CX10 • CCX01) (ε) B96.proved) Eq.refl Eq.refl

p2 : CX01 • CX10 • CCX01 • X1 ≈ CX10 • CCX01 • X0 • SWAP01
p2 = trans (sym p0) p1

p3 : CX01 • CX10 • CCX01 • X1 ≈ CX01 • CX10 • CCX01 • X1
p3 = refl

p4 : CX10 • CCX01 • X0 • SWAP01 ≈ X0 • CCX01 • CX10 • SWAP01
p4 = by-assoc-and (under (ε) (SWAP01) B366.proved) Eq.refl Eq.refl

p5 : X0 • CCX01 • CX10 • SWAP01 ≈ X0 • CCX01 • CX01 • CX10
p5 = by-assoc-and (under (X0 • CCX01) (ε) B42.proved) Eq.refl Eq.refl

p6 : CX10 • CCX01 • X0 • SWAP01 ≈ X0 • CCX01 • CX01 • CX10
p6 = trans p4 (trans p5 (refl))

p7 : CX01 • CX10 • CCX01 • X1 ≈ X0 • CCX01 • CX01 • CX10
p7 = trans (sym p3) (trans p2 p6)

proved : CX01 • CX10 • CCX01 • X1 ≈ X0 • CCX01 • CX01 • CX10
proved = p7
