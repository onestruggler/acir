{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0002 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (SWAP02 ; _•_ ; _≈_ ; refl ; sym ; trans ; ε)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP02 as Telim_SWAP02
p0 : SWAP02 • SWAP02 ≈ ε
p0 = Telim_SWAP02.proved

p1 : SWAP02 • SWAP02 ≈ SWAP02 • SWAP02
p1 = refl

p2 : ε ≈ ε
p2 = refl

p3 : SWAP02 • SWAP02 ≈ ε
p3 = trans (sym p1) (trans p0 p2)

proved : SWAP02 • SWAP02 ≈ ε
proved = p3
