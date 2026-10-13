{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Proofs.KB0074 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Proofs.KB0057 as B57
import Examples.Groups.CCX+HH-3qubit.Proofs.KB0073 as B73

p0 : X1 • X1 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01
p0 = by-assoc-and (under (ε) (SWAP01) B73.proved) Eq.refl Eq.refl

p1 : X1 • X1 • SWAP01 • SWAP01 ≈ X1 • X1
p1 = by-assoc-and (under (X1 • X1) (ε) B57.proved) Eq.refl Eq.refl

p2 : SWAP01 • SWAP01 ≈ X1 • X1
p2 = trans (sym p0) p1

p3 : SWAP01 • SWAP01 ≈ ε
p3 = by-assoc-and (under (ε) (ε) B57.proved) Eq.refl Eq.refl

p4 : SWAP01 • SWAP01 ≈ ε
p4 = trans p3 (refl)

p5 : X1 • X1 ≈ X1 • X1
p5 = refl

p6 : ε ≈ X1 • X1
p6 = trans (sym p4) (trans p2 p5)

p7 : X1 • X1 ≈ ε
p7 = sym p6

proved : X1 • X1 ≈ ε
proved = p7
