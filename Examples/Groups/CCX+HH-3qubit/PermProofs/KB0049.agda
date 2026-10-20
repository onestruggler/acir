{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0049 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (SWAP01 ; SWAP02 ; SWAP12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0002 as B2
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0048 as B48

p0 : SWAP02 • SWAP02 • SWAP12 • SWAP02 ≈ SWAP02 • SWAP01
p0 = by-assoc-and (under (SWAP02) (ε) B48.proved) Eq.refl Eq.refl

p1 : SWAP02 • SWAP02 • SWAP12 • SWAP02 ≈ SWAP12 • SWAP02
p1 = by-assoc-and (under (ε) (SWAP12 • SWAP02) B2.proved) Eq.refl Eq.refl

p2 : SWAP02 • SWAP01 ≈ SWAP12 • SWAP02
p2 = trans (sym p0) p1

p3 : SWAP02 • SWAP01 ≈ SWAP02 • SWAP01
p3 = refl

p4 : SWAP12 • SWAP02 ≈ SWAP12 • SWAP02
p4 = refl

p5 : SWAP02 • SWAP01 ≈ SWAP12 • SWAP02
p5 = trans (sym p3) (trans p2 p4)

p6 : SWAP12 • SWAP02 ≈ SWAP02 • SWAP01
p6 = sym p5

proved : SWAP12 • SWAP02 ≈ SWAP02 • SWAP01
proved = p6
