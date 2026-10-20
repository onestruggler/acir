{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0042 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX10 ; SWAP01 ; _•_ ; _≈_ ; refl ; sym ; trans)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.drel161 as Tdrel161
p0 : CX01 • CX10 ≈ CX10 • SWAP01
p0 = Tdrel161.proved

p1 : CX01 • CX10 ≈ CX01 • CX10
p1 = refl

p2 : CX10 • SWAP01 ≈ CX10 • SWAP01
p2 = refl

p3 : CX01 • CX10 ≈ CX10 • SWAP01
p3 = trans (sym p1) (trans p0 p2)

p4 : CX10 • SWAP01 ≈ CX01 • CX10
p4 = sym p3

proved : CX10 • SWAP01 ≈ CX01 • CX10
proved = p4
