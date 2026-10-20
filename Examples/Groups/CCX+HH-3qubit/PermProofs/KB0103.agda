{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0103 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX12 ; SWAP02 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r032 ; refl ; sym ; trans ; module Eq)
open K

p0 : CCX01 ≈ SWAP02 • CCX12 • SWAP02
p0 = by-assoc-and (axiom r032) Eq.refl Eq.refl

p1 : CCX01 ≈ CCX01
p1 = refl

p2 : SWAP02 • CCX12 • SWAP02 ≈ SWAP02 • CCX12 • SWAP02
p2 = refl

p3 : CCX01 ≈ SWAP02 • CCX12 • SWAP02
p3 = trans (sym p1) (trans p0 p2)

p4 : SWAP02 • CCX12 • SWAP02 ≈ CCX01
p4 = sym p3

proved : SWAP02 • CCX12 • SWAP02 ≈ CCX01
proved = p4
