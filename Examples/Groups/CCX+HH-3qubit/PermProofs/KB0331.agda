{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0331 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0010 as B10
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0213 as B213
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0217 as B217

p0 : CCX02 • CCX01 • CCX02 • CCX02 ≈ CX21 • CCX01 • CX21 • CCX02
p0 = by-assoc-and (under (ε) (CCX02) B213.proved) Eq.refl Eq.refl

p1 : CCX02 • CCX01 • CCX02 • CCX02 ≈ CCX02 • CCX01
p1 = by-assoc-and (under (CCX02 • CCX01) (ε) B10.proved) Eq.refl Eq.refl

p2 : CX21 • CCX01 • CX21 • CCX02 ≈ CCX02 • CCX01
p2 = trans (sym p0) p1

p3 : CX21 • CCX01 • CX21 • CCX02 ≈ CX12 • CCX02 • CX12 • CCX02
p3 = by-assoc-and (under (ε) (CCX02) B217.proved) Eq.refl Eq.refl

p4 : CX21 • CCX01 • CX21 • CCX02 ≈ CX12 • CCX02 • CX12 • CCX02
p4 = trans p3 (refl)

p5 : CCX02 • CCX01 ≈ CCX02 • CCX01
p5 = refl

p6 : CX12 • CCX02 • CX12 • CCX02 ≈ CCX02 • CCX01
p6 = trans (sym p4) (trans p2 p5)

proved : CX12 • CCX02 • CX12 • CCX02 ≈ CCX02 • CCX01
proved = p6
