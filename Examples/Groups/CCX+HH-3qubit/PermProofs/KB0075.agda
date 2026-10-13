{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0075 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

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
