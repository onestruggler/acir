{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Proofs.KB0073 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (SWAP01 ; X0 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Proofs.KB0000 as B0
import Examples.Groups.CCX+HH-3qubit.Proofs.KB0062 as B62

p0 : SWAP01 • X0 • X0 ≈ X1 • SWAP01 • X0
p0 = by-assoc-and (under (ε) (X0) B62.proved) Eq.refl Eq.refl

p1 : SWAP01 • X0 • X0 ≈ SWAP01
p1 = by-assoc-and (under (SWAP01) (ε) B0.proved) Eq.refl Eq.refl

p2 : X1 • SWAP01 • X0 ≈ SWAP01
p2 = trans (sym p0) p1

p3 : X1 • SWAP01 • X0 ≈ X1 • X1 • SWAP01
p3 = by-assoc-and (under (X1) (ε) B62.proved) Eq.refl Eq.refl

p4 : X1 • SWAP01 • X0 ≈ X1 • X1 • SWAP01
p4 = trans p3 (refl)

p5 : SWAP01 ≈ SWAP01
p5 = refl

p6 : X1 • X1 • SWAP01 ≈ SWAP01
p6 = trans (sym p4) (trans p2 p5)

proved : X1 • X1 • SWAP01 ≈ SWAP01
proved = p6
