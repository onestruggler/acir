{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0046 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX12 ; X0 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r037 ; refl ; sym ; trans ; module Eq)
open K

p0 : X0 • CCX12 ≈ CCX12 • X0
p0 = by-assoc-and (axiom r037) Eq.refl Eq.refl

p1 : X0 • CCX12 ≈ X0 • CCX12
p1 = refl

p2 : CCX12 • X0 ≈ CCX12 • X0
p2 = refl

p3 : X0 • CCX12 ≈ CCX12 • X0
p3 = trans (sym p1) (trans p0 p2)

p4 : CCX12 • X0 ≈ X0 • CCX12
p4 = sym p3

proved : CCX12 • X0 ≈ X0 • CCX12
proved = p4
