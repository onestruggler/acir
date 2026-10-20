{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1256 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX12 ; CX02 ; CX20 ; SWAP02 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0008 as B8
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0211 as B211
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0271 as B271
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0276 as B276
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0324 as B324

p0 : CCX01 • CCX12 • CCX01 • CX20 ≈ CCX01 • CX20 • CCX01 • CCX12
p0 = by-assoc-and (under (CCX01) (ε) B324.proved) Eq.refl Eq.refl

p1 : CCX01 • CCX12 • CCX01 • CX20 ≈ CX02 • CCX12 • CX02 • CX20
p1 = by-assoc-and (under (ε) (CX20) B211.proved) Eq.refl Eq.refl

p2 : CCX01 • CX20 • CCX01 • CCX12 ≈ CX02 • CCX12 • CX02 • CX20
p2 = trans (sym p0) p1

p3 : CCX01 • CX20 • CCX01 • CCX12 ≈ CCX01 • CX20 • CCX01 • CCX12
p3 = refl

p4 : CX02 • CCX12 • CX02 • CX20 ≈ CX02 • CX20 • CCX12 • SWAP02
p4 = by-assoc-and (under (CX02) (ε) B271.proved) Eq.refl Eq.refl

p5 : CX02 • CX20 • CCX12 • SWAP02 ≈ CX02 • CX02 • CX20 • CCX01
p5 = by-assoc-and (under (CX02) (ε) B276.proved) Eq.refl Eq.refl

p6 : CX02 • CX02 • CX20 • CCX01 ≈ CX20 • CCX01
p6 = by-assoc-and (under (ε) (CX20 • CCX01) B8.proved) Eq.refl Eq.refl

p7 : CX02 • CCX12 • CX02 • CX20 ≈ CX20 • CCX01
p7 = trans p4 (trans p5 (trans p6 (refl)))

p8 : CCX01 • CX20 • CCX01 • CCX12 ≈ CX20 • CCX01
p8 = trans (sym p3) (trans p2 p7)

proved : CCX01 • CX20 • CCX01 • CCX12 ≈ CX20 • CCX01
proved = p8
