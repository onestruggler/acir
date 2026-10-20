{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.decodeCX01 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CX01 ; CX02 ; CX12 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0010 as B10
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0028 as B28
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0035 as B35
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0137 as B137
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0150 as B150
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0214 as B214
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0307 as B307
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1438 as B1438

p0 : CX01 ≈ CX01
p0 = refl

p1 : CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX12 • CCX02 • CX12 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
p1 = by-assoc-and (under (ε) (X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) B214.proved) Eq.refl Eq.refl

p2 : CX12 • CCX02 • CX12 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X1 • CCX01 • CX01 • CCX02 • X1 • CCX01 • CCX01 • CCX02 • CCX01
p2 = by-assoc-and (under (ε) (X1 • CCX01 • CCX01 • CCX02 • CCX01) B1438.proved) Eq.refl Eq.refl

p3 : X1 • CCX01 • CX01 • CCX02 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X1 • CCX01 • CX01 • X1 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01
p3 = by-assoc-and (under (X1 • CCX01 • CX01) (CCX01 • CCX01 • CCX02 • CCX01) B28.proved) Eq.refl Eq.refl

p4 : X1 • CCX01 • CX01 • X1 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X1 • CCX01 • X1 • CX01 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01
p4 = by-assoc-and (under (X1 • CCX01) (CCX02 • CCX01 • CCX01 • CCX02 • CCX01) B35.proved) Eq.refl Eq.refl

p5 : X1 • CCX01 • X1 • CX01 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX02 • CCX01 • CX01 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01
p5 = by-assoc-and (under (ε) (CX01 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01) B150.proved) Eq.refl Eq.refl

p6 : CX02 • CCX01 • CX01 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX01 • CCX01 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01
p6 = by-assoc-and (under (ε) (CCX02 • CCX01 • CCX01 • CCX02 • CCX01) B137.proved) Eq.refl Eq.refl

p7 : CX01 • CCX01 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX01 • CX12 • CCX02 • CX12 • CCX01 • CCX02 • CCX01
p7 = by-assoc-and (under (CX01) (CCX01 • CCX02 • CCX01) B214.proved) Eq.refl Eq.refl

p8 : CX01 • CX12 • CCX02 • CX12 • CCX01 • CCX02 • CCX01 ≈ CX01 • CCX01 • CCX02 • CCX02 • CCX01
p8 = by-assoc-and (under (CX01) (CCX02 • CCX01) B307.proved) Eq.refl Eq.refl

p9 : CX01 • CCX01 • CCX02 • CCX02 • CCX01 ≈ CX01 • CCX01 • CCX01
p9 = by-assoc-and (under (CX01 • CCX01) (CCX01) B10.proved) Eq.refl Eq.refl

p10 : CX01 • CCX01 • CCX01 ≈ CX01
p10 = by-assoc-and (under (CX01) (ε) B11.proved) Eq.refl Eq.refl

p11 : CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX01
p11 = trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (refl))))))))))

proved : CX01 ≈ CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
proved = trans p0 (sym p11)
