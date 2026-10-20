{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0231 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; X0 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0028 as B28
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0044 as B44

p0 : CCX02 • X1 • X0 ≈ CCX02 • X0 • X1
p0 = by-assoc-and (under (CCX02) (ε) B44.proved) Eq.refl Eq.refl

p1 : CCX02 • X1 • X0 ≈ X1 • CCX02 • X0
p1 = by-assoc-and (under (ε) (X0) B28.proved) Eq.refl Eq.refl

p2 : CCX02 • X0 • X1 ≈ X1 • CCX02 • X0
p2 = trans (sym p0) p1

p3 : CCX02 • X0 • X1 ≈ CCX02 • X0 • X1
p3 = refl

p4 : X1 • CCX02 • X0 ≈ X1 • CCX02 • X0
p4 = refl

p5 : CCX02 • X0 • X1 ≈ X1 • CCX02 • X0
p5 = trans (sym p3) (trans p2 p4)

proved : CCX02 • X0 • X1 ≈ X1 • CCX02 • X0
proved = p5
