{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0307 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0213 as B213
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0217 as B217

p0 : CCX01 • CCX02 ≈ CCX02 • CCX01 • CCX02 • CCX01
p0 = by-assoc-and (axiom r046) Eq.refl Eq.refl

p1 : CCX01 • CCX02 ≈ CCX01 • CCX02
p1 = refl

p2 : CCX02 • CCX01 • CCX02 • CCX01 ≈ CX21 • CCX01 • CX21 • CCX01
p2 = by-assoc-and (under (ε) (CCX01) B213.proved) Eq.refl Eq.refl

p3 : CX21 • CCX01 • CX21 • CCX01 ≈ CX12 • CCX02 • CX12 • CCX01
p3 = by-assoc-and (under (ε) (CCX01) B217.proved) Eq.refl Eq.refl

p4 : CCX02 • CCX01 • CCX02 • CCX01 ≈ CX12 • CCX02 • CX12 • CCX01
p4 = trans p2 (trans p3 (refl))

p5 : CCX01 • CCX02 ≈ CX12 • CCX02 • CX12 • CCX01
p5 = trans (sym p1) (trans p0 p4)

p6 : CX12 • CCX02 • CX12 • CCX01 ≈ CCX01 • CCX02
p6 = sym p5

proved : CX12 • CCX02 • CX12 • CCX01 ≈ CCX01 • CCX02
proved = p6
