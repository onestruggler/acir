{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0017 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_SWAP_c as Tbifunct_X_SWAP_c
p0 : X1 • SWAP02 ≈ SWAP02 • X1
p0 = Tbifunct_X_SWAP_c.proved

p1 : X1 • SWAP02 ≈ X1 • SWAP02
p1 = refl

p2 : SWAP02 • X1 ≈ SWAP02 • X1
p2 = refl

p3 : X1 • SWAP02 ≈ SWAP02 • X1
p3 = trans (sym p1) (trans p0 p2)

p4 : SWAP02 • X1 ≈ X1 • SWAP02
p4 = sym p3

proved : SWAP02 • X1 ≈ X1 • SWAP02
proved = p4
