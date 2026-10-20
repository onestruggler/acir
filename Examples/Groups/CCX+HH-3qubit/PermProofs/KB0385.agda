{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0385 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX02 ; CX12 ; X0 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0027 as B27
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0037 as B37
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0121 as B121

p0 : X0 • CX12 • CCX01 • CX02 ≈ CCX01 • X0 • CX02
p0 = by-assoc-and (under (ε) (CX02) B121.proved) Eq.refl Eq.refl

p1 : X0 • CX12 • CCX01 • CX02 ≈ X0 • CX12 • CX02 • CCX01
p1 = by-assoc-and (under (X0 • CX12) (ε) B37.proved) Eq.refl Eq.refl

p2 : CCX01 • X0 • CX02 ≈ X0 • CX12 • CX02 • CCX01
p2 = trans (sym p0) p1

p3 : CCX01 • X0 • CX02 ≈ CCX01 • X0 • CX02
p3 = refl

p4 : X0 • CX12 • CX02 • CCX01 ≈ X0 • CX02 • CX12 • CCX01
p4 = by-assoc-and (under (X0) (CCX01) B27.proved) Eq.refl Eq.refl

p5 : X0 • CX12 • CX02 • CCX01 ≈ X0 • CX02 • CX12 • CCX01
p5 = trans p4 (refl)

p6 : CCX01 • X0 • CX02 ≈ X0 • CX02 • CX12 • CCX01
p6 = trans (sym p3) (trans p2 p5)

p7 : X0 • CX02 • CX12 • CCX01 ≈ CCX01 • X0 • CX02
p7 = sym p6

proved : X0 • CX02 • CX12 • CCX01 ≈ CCX01 • X0 • CX02
proved = p7
