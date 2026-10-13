{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Proofs.KB0056 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Proofs.KB0030 as B30
import Examples.Groups.CCX+HH-3qubit.Proofs.KB0053 as B53

p0 : CX10 • CX10 • CX01 ≈ CX01
p0 = by-assoc-and (under (ε) (CX01) B53.proved) Eq.refl Eq.refl

p1 : CX10 • CX10 • CX01 ≈ CX10 • CX01 • SWAP01
p1 = by-assoc-and (under (CX10) (ε) B30.proved) Eq.refl Eq.refl

p2 : CX01 ≈ CX10 • CX01 • SWAP01
p2 = trans (sym p0) p1

p3 : CX01 ≈ CX01
p3 = refl

p4 : CX10 • CX01 • SWAP01 ≈ CX01 • SWAP01 • SWAP01
p4 = by-assoc-and (under (ε) (SWAP01) B30.proved) Eq.refl Eq.refl

p5 : CX10 • CX01 • SWAP01 ≈ CX01 • SWAP01 • SWAP01
p5 = trans p4 (refl)

p6 : CX01 ≈ CX01 • SWAP01 • SWAP01
p6 = trans (sym p3) (trans p2 p5)

p7 : CX01 • SWAP01 • SWAP01 ≈ CX01
p7 = sym p6

proved : CX01 • SWAP01 • SWAP01 ≈ CX01
proved = p7
