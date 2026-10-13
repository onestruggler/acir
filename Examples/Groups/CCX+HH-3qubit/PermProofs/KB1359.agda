{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1359 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0716 as B716
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1357 as B1357

p0 : CCX12 • CX21 • CCX01 • CX20 • CCX02 ≈ CX21 • CCX01 • CCX12 • CCX02
p0 = by-assoc-and (under (ε) (CCX02) B1357.proved) Eq.refl Eq.refl

p1 : CCX12 • CX21 • CCX01 • CX20 • CCX02 ≈ CCX12 • CCX02 • CCX01 • CX20
p1 = by-assoc-and (under (CCX12) (ε) B716.proved) Eq.refl Eq.refl

p2 : CX21 • CCX01 • CCX12 • CCX02 ≈ CCX12 • CCX02 • CCX01 • CX20
p2 = trans (sym p0) p1

p3 : CX21 • CCX01 • CCX12 • CCX02 ≈ CX21 • CCX01 • CCX12 • CCX02
p3 = refl

p4 : CCX12 • CCX02 • CCX01 • CX20 ≈ CCX12 • CCX02 • CCX01 • CX20
p4 = refl

p5 : CX21 • CCX01 • CCX12 • CCX02 ≈ CCX12 • CCX02 • CCX01 • CX20
p5 = trans (sym p3) (trans p2 p4)

p6 : CCX12 • CCX02 • CCX01 • CX20 ≈ CX21 • CCX01 • CCX12 • CCX02
p6 = sym p5

proved : CCX12 • CCX02 • CCX01 • CX20 ≈ CX21 • CCX01 • CCX12 • CCX02
proved = p6
