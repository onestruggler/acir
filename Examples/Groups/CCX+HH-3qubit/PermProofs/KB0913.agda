{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0913 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CX01 ; CX21 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0018 as B18
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0019 as B19
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0188 as B188
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0190 as B190
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0231 as B231
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0905 as B905

p0 : CCX02 • X2 • CX01 • X0 • X1 ≈ CCX02 • X2 • X0 • CX01
p0 = by-assoc-and (under (CCX02 • X2) (ε) B190.proved) Eq.refl Eq.refl

p1 : CCX02 • X2 • CX01 • X0 • X1 ≈ X2 • CCX02 • X0 • X1
p1 = by-assoc-and (under (ε) (X0 • X1) B188.proved) Eq.refl Eq.refl

p2 : CCX02 • X2 • X0 • CX01 ≈ X2 • CCX02 • X0 • X1
p2 = trans (sym p0) p1

p3 : CCX02 • X2 • X0 • CX01 ≈ CCX02 • X0 • X2 • CX01
p3 = by-assoc-and (under (CCX02) (CX01) B18.proved) Eq.refl Eq.refl

p4 : CCX02 • X0 • X2 • CX01 ≈ X0 • CX21 • X2 • CCX02
p4 = by-assoc-and (under (ε) (ε) B905.proved) Eq.refl Eq.refl

p5 : CCX02 • X2 • X0 • CX01 ≈ X0 • CX21 • X2 • CCX02
p5 = trans p3 (trans p4 (refl))

p6 : X2 • CCX02 • X0 • X1 ≈ X2 • X1 • CCX02 • X0
p6 = by-assoc-and (under (X2) (ε) B231.proved) Eq.refl Eq.refl

p7 : X2 • X1 • CCX02 • X0 ≈ X1 • X2 • CCX02 • X0
p7 = by-assoc-and (under (ε) (CCX02 • X0) B19.proved) Eq.refl Eq.refl

p8 : X2 • CCX02 • X0 • X1 ≈ X1 • X2 • CCX02 • X0
p8 = trans p6 (trans p7 (refl))

p9 : X0 • CX21 • X2 • CCX02 ≈ X1 • X2 • CCX02 • X0
p9 = trans (sym p5) (trans p2 p8)

p10 : X1 • X2 • CCX02 • X0 ≈ X0 • CX21 • X2 • CCX02
p10 = sym p9

proved : X1 • X2 • CCX02 • X0 ≈ X0 • CX21 • X2 • CCX02
proved = p10
