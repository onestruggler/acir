{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0096 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (SWAP01 ; X0 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0000 as B0
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0095 as B95

p0 : SWAP01 • SWAP01 • X0 • SWAP01 ≈ SWAP01 • X1
p0 = by-assoc-and (under (SWAP01) (ε) B95.proved) Eq.refl Eq.refl

p1 : SWAP01 • SWAP01 • X0 • SWAP01 ≈ X0 • SWAP01
p1 = by-assoc-and (under (ε) (X0 • SWAP01) B0.proved) Eq.refl Eq.refl

p2 : SWAP01 • X1 ≈ X0 • SWAP01
p2 = trans (sym p0) p1

p3 : SWAP01 • X1 ≈ SWAP01 • X1
p3 = refl

p4 : X0 • SWAP01 ≈ X0 • SWAP01
p4 = refl

p5 : SWAP01 • X1 ≈ X0 • SWAP01
p5 = trans (sym p3) (trans p2 p4)

proved : SWAP01 • X1 ≈ X0 • SWAP01
proved = p5
