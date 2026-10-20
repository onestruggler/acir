{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.braid5 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CX12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0214 as B214
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0307 as B307
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0331 as B331

p0 : CCX01 • CCX02 • CCX01 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX12 • CCX02 • CX12 • CCX01 • CCX01 • CCX02 • CCX01
p0 = by-assoc-and (under (ε) (CCX01 • CCX01 • CCX02 • CCX01) B214.proved) Eq.refl Eq.refl

p1 : CX12 • CCX02 • CX12 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CCX01 • CCX02 • CCX01 • CCX02 • CCX01
p1 = by-assoc-and (under (ε) (CCX01 • CCX02 • CCX01) B307.proved) Eq.refl Eq.refl

p2 : CCX01 • CCX02 • CCX01 • CCX02 • CCX01 ≈ CX12 • CCX02 • CX12 • CCX02 • CCX01
p2 = by-assoc-and (under (ε) (CCX02 • CCX01) B214.proved) Eq.refl Eq.refl

p3 : CX12 • CCX02 • CX12 • CCX02 • CCX01 ≈ CCX02 • CCX01 • CCX01
p3 = by-assoc-and (under (ε) (CCX01) B331.proved) Eq.refl Eq.refl

p4 : CCX02 • CCX01 • CCX01 ≈ CCX02
p4 = by-assoc-and (under (CCX02) (ε) B11.proved) Eq.refl Eq.refl

p5 : CCX01 • CCX02 • CCX01 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CCX02
p5 = trans p0 (trans p1 (trans p2 (trans p3 (trans p4 (refl)))))

p6 : CCX01 • CCX01 • CCX02 • CCX01 • CCX01 ≈ CCX02 • CCX01 • CCX01
p6 = by-assoc-and (under (ε) (CCX02 • CCX01 • CCX01) B11.proved) Eq.refl Eq.refl

p7 : CCX02 • CCX01 • CCX01 ≈ CCX02
p7 = by-assoc-and (under (CCX02) (ε) B11.proved) Eq.refl Eq.refl

p8 : CCX01 • CCX01 • CCX02 • CCX01 • CCX01 ≈ CCX02
p8 = trans p6 (trans p7 (refl))

proved : CCX01 • CCX02 • CCX01 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CCX01 • CCX01 • CCX02 • CCX01 • CCX01
proved = trans p5 (sym p8)
