{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0001 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (SWAP12 ; _•_ ; _≈_ ; refl ; sym ; trans ; ε)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP12 as Telim_SWAP12
p0 : SWAP12 • SWAP12 ≈ ε
p0 = Telim_SWAP12.proved

p1 : SWAP12 • SWAP12 ≈ SWAP12 • SWAP12
p1 = refl

p2 : ε ≈ ε
p2 = refl

p3 : SWAP12 • SWAP12 ≈ ε
p3 = trans (sym p1) (trans p0 p2)

proved : SWAP12 • SWAP12 ≈ ε
proved = p3
