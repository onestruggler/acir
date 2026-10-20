{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1335 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX10 ; CX12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0147 as B147
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0219 as B219
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0624 as B624

p0 : CX10 • CX12 • CCX01 • CCX02 • CX10 ≈ CX10 • CCX02 • CX10 • CCX01
p0 = by-assoc-and (under (CX10) (ε) B624.proved) Eq.refl Eq.refl

p1 : CX10 • CX12 • CCX01 • CCX02 • CX10 ≈ CCX01 • CX10 • CCX02 • CX10
p1 = by-assoc-and (under (ε) (CCX02 • CX10) B147.proved) Eq.refl Eq.refl

p2 : CX10 • CCX02 • CX10 • CCX01 ≈ CCX01 • CX10 • CCX02 • CX10
p2 = trans (sym p0) p1

p3 : CX10 • CCX02 • CX10 • CCX01 ≈ CX01 • CCX12 • CX01 • CCX01
p3 = by-assoc-and (under (ε) (CCX01) B219.proved) Eq.refl Eq.refl

p4 : CX10 • CCX02 • CX10 • CCX01 ≈ CX01 • CCX12 • CX01 • CCX01
p4 = trans p3 (refl)

p5 : CCX01 • CX10 • CCX02 • CX10 ≈ CCX01 • CX01 • CCX12 • CX01
p5 = by-assoc-and (under (CCX01) (ε) B219.proved) Eq.refl Eq.refl

p6 : CCX01 • CX10 • CCX02 • CX10 ≈ CCX01 • CX01 • CCX12 • CX01
p6 = trans p5 (refl)

p7 : CX01 • CCX12 • CX01 • CCX01 ≈ CCX01 • CX01 • CCX12 • CX01
p7 = trans (sym p4) (trans p2 p6)

p8 : CCX01 • CX01 • CCX12 • CX01 ≈ CX01 • CCX12 • CX01 • CCX01
p8 = sym p7

proved : CCX01 • CX01 • CCX12 • CX01 ≈ CX01 • CCX12 • CX01 • CCX01
proved = p8
