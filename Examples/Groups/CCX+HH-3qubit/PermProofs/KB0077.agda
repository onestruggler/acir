{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0077 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CCX_g as Tsymmetry_CCX_g
p0 : CCX12 ≈ SWAP12 • CCX12 • SWAP12
p0 = Tsymmetry_CCX_g.proved

p1 : CCX12 ≈ CCX12
p1 = refl

p2 : SWAP12 • CCX12 • SWAP12 ≈ SWAP12 • CCX12 • SWAP12
p2 = refl

p3 : CCX12 ≈ SWAP12 • CCX12 • SWAP12
p3 = trans (sym p1) (trans p0 p2)

p4 : SWAP12 • CCX12 • SWAP12 ≈ CCX12
p4 = sym p3

proved : SWAP12 • CCX12 • SWAP12 ≈ CCX12
proved = p4
