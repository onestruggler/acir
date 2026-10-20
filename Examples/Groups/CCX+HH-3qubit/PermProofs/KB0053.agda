{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0053 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (SWAP01 ; SWAP02 ; SWAP12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0000 as B0
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0051 as B51

p0 : SWAP01 • SWAP12 • SWAP01 • SWAP01 ≈ SWAP02 • SWAP01
p0 = by-assoc-and (under (ε) (SWAP01) B51.proved) Eq.refl Eq.refl

p1 : SWAP01 • SWAP12 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP12
p1 = by-assoc-and (under (SWAP01 • SWAP12) (ε) B0.proved) Eq.refl Eq.refl

p2 : SWAP02 • SWAP01 ≈ SWAP01 • SWAP12
p2 = trans (sym p0) p1

p3 : SWAP02 • SWAP01 ≈ SWAP02 • SWAP01
p3 = refl

p4 : SWAP01 • SWAP12 ≈ SWAP01 • SWAP12
p4 = refl

p5 : SWAP02 • SWAP01 ≈ SWAP01 • SWAP12
p5 = trans (sym p3) (trans p2 p4)

proved : SWAP02 • SWAP01 ≈ SWAP01 • SWAP12
proved = p5
