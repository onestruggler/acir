{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0075 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; SWAP02 ; _•_ ; _≈_ ; refl ; sym ; trans)
open K

import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CCX_f as Tsymmetry_CCX_f
p0 : CCX02 ≈ SWAP02 • CCX02 • SWAP02
p0 = Tsymmetry_CCX_f.proved

p1 : CCX02 ≈ CCX02
p1 = refl

p2 : SWAP02 • CCX02 • SWAP02 ≈ SWAP02 • CCX02 • SWAP02
p2 = refl

p3 : CCX02 ≈ SWAP02 • CCX02 • SWAP02
p3 = trans (sym p1) (trans p0 p2)

p4 : SWAP02 • CCX02 • SWAP02 ≈ CCX02
p4 = sym p3

proved : SWAP02 • CCX02 • SWAP02 ≈ CCX02
proved = p4
