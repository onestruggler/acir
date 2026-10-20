{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1357 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX12 ; CX20 ; CX21 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0043 as B43
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0179 as B179
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0323 as B323

p0 : CX21 • CX20 • CCX12 • CCX01 • CX20 ≈ CX21 • CCX01 • CCX12
p0 = by-assoc-and (under (CX21) (ε) B323.proved) Eq.refl Eq.refl

p1 : CX21 • CX20 • CCX12 • CCX01 • CX20 ≈ CX20 • CX21 • CCX12 • CCX01 • CX20
p1 = by-assoc-and (under (ε) (CCX12 • CCX01 • CX20) B43.proved) Eq.refl Eq.refl

p2 : CX21 • CCX01 • CCX12 ≈ CX20 • CX21 • CCX12 • CCX01 • CX20
p2 = trans (sym p0) p1

p3 : CX21 • CCX01 • CCX12 ≈ CX21 • CCX01 • CCX12
p3 = refl

p4 : CX20 • CX21 • CCX12 • CCX01 • CX20 ≈ CCX12 • CX21 • CCX01 • CX20
p4 = by-assoc-and (under (ε) (CCX01 • CX20) B179.proved) Eq.refl Eq.refl

p5 : CX20 • CX21 • CCX12 • CCX01 • CX20 ≈ CCX12 • CX21 • CCX01 • CX20
p5 = trans p4 (refl)

p6 : CX21 • CCX01 • CCX12 ≈ CCX12 • CX21 • CCX01 • CX20
p6 = trans (sym p3) (trans p2 p5)

p7 : CCX12 • CX21 • CCX01 • CX20 ≈ CX21 • CCX01 • CCX12
p7 = sym p6

proved : CCX12 • CX21 • CCX01 • CX20 ≈ CX21 • CCX01 • CCX12
proved = p7
