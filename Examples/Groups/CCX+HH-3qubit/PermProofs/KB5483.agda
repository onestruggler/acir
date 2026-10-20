{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB5483 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0010 as B10
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB5482 as B5482

p0 : CCX01 • CCX02 • CCX12 • CCX01 • CCX02 • CCX02 ≈ CCX02 • CCX12 • CCX01 • CCX02
p0 = by-assoc-and (under (ε) (CCX02) B5482.proved) Eq.refl Eq.refl

p1 : CCX01 • CCX02 • CCX12 • CCX01 • CCX02 • CCX02 ≈ CCX01 • CCX02 • CCX12 • CCX01
p1 = by-assoc-and (under (CCX01 • CCX02 • CCX12 • CCX01) (ε) B10.proved) Eq.refl Eq.refl

p2 : CCX02 • CCX12 • CCX01 • CCX02 ≈ CCX01 • CCX02 • CCX12 • CCX01
p2 = trans (sym p0) p1

p3 : CCX02 • CCX12 • CCX01 • CCX02 ≈ CCX02 • CCX12 • CCX01 • CCX02
p3 = refl

p4 : CCX01 • CCX02 • CCX12 • CCX01 ≈ CCX01 • CCX02 • CCX12 • CCX01
p4 = refl

p5 : CCX02 • CCX12 • CCX01 • CCX02 ≈ CCX01 • CCX02 • CCX12 • CCX01
p5 = trans (sym p3) (trans p2 p4)

proved : CCX02 • CCX12 • CCX01 • CCX02 ≈ CCX01 • CCX02 • CCX12 • CCX01
proved = p5
