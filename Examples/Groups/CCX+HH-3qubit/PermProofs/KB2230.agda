{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB2230 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CX01 ; X0 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0029 as B29
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0485 as B485

p0 : CCX01 • X2 • CCX02 • X0 • X2 ≈ CCX01 • CX01 • CCX02 • X0
p0 = by-assoc-and (under (CCX01) (ε) B485.proved) Eq.refl Eq.refl

p1 : CCX01 • X2 • CCX02 • X0 • X2 ≈ X2 • CCX01 • CCX02 • X0 • X2
p1 = by-assoc-and (under (ε) (CCX02 • X0 • X2) B29.proved) Eq.refl Eq.refl

p2 : CCX01 • CX01 • CCX02 • X0 ≈ X2 • CCX01 • CCX02 • X0 • X2
p2 = trans (sym p0) p1

p3 : CCX01 • CX01 • CCX02 • X0 ≈ CCX01 • CX01 • CCX02 • X0
p3 = refl

p4 : X2 • CCX01 • CCX02 • X0 • X2 ≈ X2 • CCX01 • CCX02 • X0 • X2
p4 = refl

p5 : CCX01 • CX01 • CCX02 • X0 ≈ X2 • CCX01 • CCX02 • X0 • X2
p5 = trans (sym p3) (trans p2 p4)

p6 : X2 • CCX01 • CCX02 • X0 • X2 ≈ CCX01 • CX01 • CCX02 • X0
p6 = sym p5

proved : X2 • CCX01 • CCX02 • X0 • X2 ≈ CCX01 • CX01 • CCX02 • X0
proved = p6
