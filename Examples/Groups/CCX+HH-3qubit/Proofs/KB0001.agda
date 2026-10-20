{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Proofs.KB0001 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r022 ; refl ; sym ; trans ; ε ; module Eq)
open K

p0 : CX01 • CX01 ≈ ε
p0 = by-assoc-and (axiom r022) Eq.refl Eq.refl

p1 : CX01 • CX01 ≈ CX01 • CX01
p1 = refl

p2 : ε ≈ ε
p2 = refl

p3 : CX01 • CX01 ≈ ε
p3 = trans (sym p1) (trans p0 p2)

proved : CX01 • CX01 ≈ ε
proved = p3
