{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0093 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0002 as B2
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0092 as B92

p0 : SWAP02 • SWAP02 • X0 • SWAP02 ≈ SWAP02 • X2
p0 = by-assoc-and (under (SWAP02) (ε) B92.proved) Eq.refl Eq.refl

p1 : SWAP02 • SWAP02 • X0 • SWAP02 ≈ X0 • SWAP02
p1 = by-assoc-and (under (ε) (X0 • SWAP02) B2.proved) Eq.refl Eq.refl

p2 : SWAP02 • X2 ≈ X0 • SWAP02
p2 = trans (sym p0) p1

p3 : SWAP02 • X2 ≈ SWAP02 • X2
p3 = refl

p4 : X0 • SWAP02 ≈ X0 • SWAP02
p4 = refl

p5 : SWAP02 • X2 ≈ X0 • SWAP02
p5 = trans (sym p3) (trans p2 p4)

proved : SWAP02 • X2 ≈ X0 • SWAP02
proved = p5
