{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Proofs.KB0057 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Proofs.KB0001 as B1
import Examples.Groups.CCX+HH-3qubit.Proofs.KB0056 as B56

p0 : CX01 • CX01 • SWAP01 • SWAP01 ≈ CX01 • CX01
p0 = by-assoc-and (under (CX01) (ε) B56.proved) Eq.refl Eq.refl

p1 : CX01 • CX01 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01
p1 = by-assoc-and (under (ε) (SWAP01 • SWAP01) B1.proved) Eq.refl Eq.refl

p2 : CX01 • CX01 ≈ SWAP01 • SWAP01
p2 = trans (sym p0) p1

p3 : CX01 • CX01 ≈ ε
p3 = by-assoc-and (under (ε) (ε) B1.proved) Eq.refl Eq.refl

p4 : CX01 • CX01 ≈ ε
p4 = trans p3 (refl)

p5 : SWAP01 • SWAP01 ≈ SWAP01 • SWAP01
p5 = refl

p6 : ε ≈ SWAP01 • SWAP01
p6 = trans (sym p4) (trans p2 p5)

p7 : SWAP01 • SWAP01 ≈ ε
p7 = sym p6

proved : SWAP01 • SWAP01 ≈ ε
proved = p7
