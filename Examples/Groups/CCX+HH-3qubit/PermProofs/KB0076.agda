{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0076 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; SWAP02 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0002 as B2
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0075 as B75

p0 : SWAP02 • SWAP02 • CCX02 • SWAP02 ≈ SWAP02 • CCX02
p0 = by-assoc-and (under (SWAP02) (ε) B75.proved) Eq.refl Eq.refl

p1 : SWAP02 • SWAP02 • CCX02 • SWAP02 ≈ CCX02 • SWAP02
p1 = by-assoc-and (under (ε) (CCX02 • SWAP02) B2.proved) Eq.refl Eq.refl

p2 : SWAP02 • CCX02 ≈ CCX02 • SWAP02
p2 = trans (sym p0) p1

p3 : SWAP02 • CCX02 ≈ SWAP02 • CCX02
p3 = refl

p4 : CCX02 • SWAP02 ≈ CCX02 • SWAP02
p4 = refl

p5 : SWAP02 • CCX02 ≈ CCX02 • SWAP02
p5 = trans (sym p3) (trans p2 p4)

proved : SWAP02 • CCX02 ≈ CCX02 • SWAP02
proved = p5
