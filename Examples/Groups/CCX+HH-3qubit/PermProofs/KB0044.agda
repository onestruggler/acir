{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0044 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (X0 ; X1 ; _•_ ; _≈_ ; refl ; sym ; trans)
open K

import Examples.Groups.CCX+HH-3qubit.Proofs.X0X1 as Pauli
p0 : X0 • X1 ≈ X1 • X0
p0 = Pauli.proved

p1 : X0 • X1 ≈ X0 • X1
p1 = refl

p2 : X1 • X0 ≈ X1 • X0
p2 = refl

p3 : X0 • X1 ≈ X1 • X0
p3 = trans (sym p1) (trans p0 p2)

p4 : X1 • X0 ≈ X0 • X1
p4 = sym p3

proved : X1 • X0 ≈ X0 • X1
proved = p4
