{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0073 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; SWAP01 ; _•_ ; _≈_ ; refl ; sym ; trans)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CCX_c as Tsymmetry_CCX_c
p0 : CCX01 ≈ SWAP01 • CCX01 • SWAP01
p0 = Tsymmetry_CCX_c.proved

p1 : CCX01 ≈ CCX01
p1 = refl

p2 : SWAP01 • CCX01 • SWAP01 ≈ SWAP01 • CCX01 • SWAP01
p2 = refl

p3 : CCX01 ≈ SWAP01 • CCX01 • SWAP01
p3 = trans (sym p1) (trans p0 p2)

p4 : SWAP01 • CCX01 • SWAP01 ≈ CCX01
p4 = sym p3

proved : SWAP01 • CCX01 • SWAP01 ≈ CCX01
proved = p4
