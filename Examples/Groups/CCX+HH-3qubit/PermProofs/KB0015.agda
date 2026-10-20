{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0015 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (SWAP12 ; X0 ; _•_ ; _≈_ ; refl ; sym ; trans)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_SWAP_a as Tbifunct_X_SWAP_a
p0 : X0 • SWAP12 ≈ SWAP12 • X0
p0 = Tbifunct_X_SWAP_a.proved

p1 : X0 • SWAP12 ≈ X0 • SWAP12
p1 = refl

p2 : SWAP12 • X0 ≈ SWAP12 • X0
p2 = refl

p3 : X0 • SWAP12 ≈ SWAP12 • X0
p3 = trans (sym p1) (trans p0 p2)

p4 : SWAP12 • X0 ≈ X0 • SWAP12
p4 = sym p3

proved : SWAP12 • X0 ≈ X0 • SWAP12
proved = p4
