{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0000 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (SWAP01 ; _•_ ; _≈_ ; refl ; sym ; trans ; ε)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as Telim_SWAP01
p0 : SWAP01 • SWAP01 ≈ ε
p0 = Telim_SWAP01.proved

p1 : SWAP01 • SWAP01 ≈ SWAP01 • SWAP01
p1 = refl

p2 : ε ≈ ε
p2 = refl

p3 : SWAP01 • SWAP01 ≈ ε
p3 = trans (sym p1) (trans p0 p2)

proved : SWAP01 • SWAP01 ≈ ε
proved = p3
