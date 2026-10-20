{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0016 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (SWAP01 ; X2 ; _•_ ; _≈_ ; refl ; sym ; trans)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_SWAP_b as Tbifunct_X_SWAP_b
p0 : X2 • SWAP01 ≈ SWAP01 • X2
p0 = Tbifunct_X_SWAP_b.proved

p1 : X2 • SWAP01 ≈ X2 • SWAP01
p1 = refl

p2 : SWAP01 • X2 ≈ SWAP01 • X2
p2 = refl

p3 : X2 • SWAP01 ≈ SWAP01 • X2
p3 = trans (sym p1) (trans p0 p2)

p4 : SWAP01 • X2 ≈ X2 • SWAP01
p4 = sym p3

proved : SWAP01 • X2 ≈ X2 • SWAP01
proved = p4
