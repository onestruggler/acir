{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.invol5 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CX12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0010 as B10
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0214 as B214
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0307 as B307

p0 : CCX01 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX12 • CCX02 • CX12 • CCX01 • CCX02 • CCX01
p0 = by-assoc-and (under (ε) (CCX01 • CCX02 • CCX01) B214.proved) Eq.refl Eq.refl

p1 : CX12 • CCX02 • CX12 • CCX01 • CCX02 • CCX01 ≈ CCX01 • CCX02 • CCX02 • CCX01
p1 = by-assoc-and (under (ε) (CCX02 • CCX01) B307.proved) Eq.refl Eq.refl

p2 : CCX01 • CCX02 • CCX02 • CCX01 ≈ CCX01 • CCX01
p2 = by-assoc-and (under (CCX01) (CCX01) B10.proved) Eq.refl Eq.refl

p3 : CCX01 • CCX01 ≈ ε
p3 = by-assoc-and (under (ε) (ε) B11.proved) Eq.refl Eq.refl

p4 : CCX01 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01 ≈ ε
p4 = trans p0 (trans p1 (trans p2 (trans p3 (refl))))

p5 : ε ≈ ε
p5 = refl

proved : CCX01 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01 ≈ ε
proved = trans p4 (sym p5)
