{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0064 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX20 ; CX21 ; SWAP01 ; _•_ ; _≈_ ; refl ; sym ; trans)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_h as Tsymmetry_CX_h
p0 : CX20 ≈ SWAP01 • CX21 • SWAP01
p0 = Tsymmetry_CX_h.proved

p1 : CX20 ≈ CX20
p1 = refl

p2 : SWAP01 • CX21 • SWAP01 ≈ SWAP01 • CX21 • SWAP01
p2 = refl

p3 : CX20 ≈ SWAP01 • CX21 • SWAP01
p3 = trans (sym p1) (trans p0 p2)

p4 : SWAP01 • CX21 • SWAP01 ≈ CX20
p4 = sym p3

proved : SWAP01 • CX21 • SWAP01 ≈ CX20
proved = p4
