{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0057 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX10 ; CX12 ; SWAP02 ; _•_ ; _≈_ ; refl ; sym ; trans)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_b as Tsymmetry_CX_b
p0 : CX10 ≈ SWAP02 • CX12 • SWAP02
p0 = Tsymmetry_CX_b.proved

p1 : CX10 ≈ CX10
p1 = refl

p2 : SWAP02 • CX12 • SWAP02 ≈ SWAP02 • CX12 • SWAP02
p2 = refl

p3 : CX10 ≈ SWAP02 • CX12 • SWAP02
p3 = trans (sym p1) (trans p0 p2)

p4 : SWAP02 • CX12 • SWAP02 ≈ CX10
p4 = sym p3

proved : SWAP02 • CX12 • SWAP02 ≈ CX10
proved = p4
