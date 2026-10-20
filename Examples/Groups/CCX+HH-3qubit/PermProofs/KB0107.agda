{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0107 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; SWAP12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0001 as B1
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0106 as B106

p0 : SWAP12 • SWAP12 • CCX02 • SWAP12 ≈ SWAP12 • CCX01
p0 = by-assoc-and (under (SWAP12) (ε) B106.proved) Eq.refl Eq.refl

p1 : SWAP12 • SWAP12 • CCX02 • SWAP12 ≈ CCX02 • SWAP12
p1 = by-assoc-and (under (ε) (CCX02 • SWAP12) B1.proved) Eq.refl Eq.refl

p2 : SWAP12 • CCX01 ≈ CCX02 • SWAP12
p2 = trans (sym p0) p1

p3 : SWAP12 • CCX01 ≈ SWAP12 • CCX01
p3 = refl

p4 : CCX02 • SWAP12 ≈ CCX02 • SWAP12
p4 = refl

p5 : SWAP12 • CCX01 ≈ CCX02 • SWAP12
p5 = trans (sym p3) (trans p2 p4)

proved : SWAP12 • CCX01 ≈ CCX02 • SWAP12
proved = p5
