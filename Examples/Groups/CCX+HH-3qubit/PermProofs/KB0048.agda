{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0048 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_SWAP01 as Tsymmetry_SWAP01
p0 : SWAP01 ≈ SWAP02 • SWAP12 • SWAP02
p0 = Tsymmetry_SWAP01.proved

p1 : SWAP01 ≈ SWAP01
p1 = refl

p2 : SWAP02 • SWAP12 • SWAP02 ≈ SWAP02 • SWAP12 • SWAP02
p2 = refl

p3 : SWAP01 ≈ SWAP02 • SWAP12 • SWAP02
p3 = trans (sym p1) (trans p0 p2)

p4 : SWAP02 • SWAP12 • SWAP02 ≈ SWAP01
p4 = sym p3

proved : SWAP02 • SWAP12 • SWAP02 ≈ SWAP01
proved = p4
