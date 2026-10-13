{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0051 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_SWAP02 as Tsymmetry_SWAP02
p0 : SWAP02 ≈ SWAP01 • SWAP12 • SWAP01
p0 = Tsymmetry_SWAP02.proved

p1 : SWAP02 ≈ SWAP02
p1 = refl

p2 : SWAP01 • SWAP12 • SWAP01 ≈ SWAP01 • SWAP12 • SWAP01
p2 = refl

p3 : SWAP02 ≈ SWAP01 • SWAP12 • SWAP01
p3 = trans (sym p1) (trans p0 p2)

p4 : SWAP01 • SWAP12 • SWAP01 ≈ SWAP02
p4 = sym p3

proved : SWAP01 • SWAP12 • SWAP01 ≈ SWAP02
proved = p4
