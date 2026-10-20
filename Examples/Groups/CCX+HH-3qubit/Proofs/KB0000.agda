{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Proofs.KB0000 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (X0 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r021 ; refl ; sym ; trans ; ε ; module Eq)
open K

p0 : X0 • X0 ≈ ε
p0 = by-assoc-and (axiom r021) Eq.refl Eq.refl

p1 : X0 • X0 ≈ X0 • X0
p1 = refl

p2 : ε ≈ ε
p2 = refl

p3 : X0 • X0 ≈ ε
p3 = trans (sym p1) (trans p0 p2)

proved : X0 • X0 ≈ ε
proved = p3
