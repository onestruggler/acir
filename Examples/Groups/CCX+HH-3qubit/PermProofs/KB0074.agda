{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0074 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; SWAP01 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0000 as B0
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0073 as B73

p0 : SWAP01 • SWAP01 • CCX01 • SWAP01 ≈ SWAP01 • CCX01
p0 = by-assoc-and (under (SWAP01) (ε) B73.proved) Eq.refl Eq.refl

p1 : SWAP01 • SWAP01 • CCX01 • SWAP01 ≈ CCX01 • SWAP01
p1 = by-assoc-and (under (ε) (CCX01 • SWAP01) B0.proved) Eq.refl Eq.refl

p2 : SWAP01 • CCX01 ≈ CCX01 • SWAP01
p2 = trans (sym p0) p1

p3 : SWAP01 • CCX01 ≈ SWAP01 • CCX01
p3 = refl

p4 : CCX01 • SWAP01 ≈ CCX01 • SWAP01
p4 = refl

p5 : SWAP01 • CCX01 ≈ CCX01 • SWAP01
p5 = trans (sym p3) (trans p2 p4)

proved : SWAP01 • CCX01 ≈ CCX01 • SWAP01
proved = p5
