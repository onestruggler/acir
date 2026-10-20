{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0067 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX21 ; SWAP02 ; _•_ ; _≈_ ; refl ; sym ; trans)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_i as Tsymmetry_CX_i
p0 : CX21 ≈ SWAP02 • CX01 • SWAP02
p0 = Tsymmetry_CX_i.proved

p1 : CX21 ≈ CX21
p1 = refl

p2 : SWAP02 • CX01 • SWAP02 ≈ SWAP02 • CX01 • SWAP02
p2 = refl

p3 : CX21 ≈ SWAP02 • CX01 • SWAP02
p3 = trans (sym p1) (trans p0 p2)

p4 : SWAP02 • CX01 • SWAP02 ≈ CX21
p4 = sym p3

proved : SWAP02 • CX01 • SWAP02 ≈ CX21
proved = p4
