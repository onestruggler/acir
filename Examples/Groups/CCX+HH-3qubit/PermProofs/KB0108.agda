{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0108 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0001 as B1
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0106 as B106

p0 : SWAP12 • CCX02 • SWAP12 • SWAP12 ≈ CCX01 • SWAP12
p0 = by-assoc-and (under (ε) (SWAP12) B106.proved) Eq.refl Eq.refl

p1 : SWAP12 • CCX02 • SWAP12 • SWAP12 ≈ SWAP12 • CCX02
p1 = by-assoc-and (under (SWAP12 • CCX02) (ε) B1.proved) Eq.refl Eq.refl

p2 : CCX01 • SWAP12 ≈ SWAP12 • CCX02
p2 = trans (sym p0) p1

p3 : CCX01 • SWAP12 ≈ CCX01 • SWAP12
p3 = refl

p4 : SWAP12 • CCX02 ≈ SWAP12 • CCX02
p4 = refl

p5 : CCX01 • SWAP12 ≈ SWAP12 • CCX02
p5 = trans (sym p3) (trans p2 p4)

p6 : SWAP12 • CCX02 ≈ CCX01 • SWAP12
p6 = sym p5

proved : SWAP12 • CCX02 ≈ CCX01 • SWAP12
proved = p6
