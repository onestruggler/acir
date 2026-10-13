{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0827 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0022 as B22
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0029 as B29
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0130 as B130
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0157 as B157

p0 : CX01 • CCX01 • CX01 • CCX02 • X2 ≈ CX02 • CCX01 • CCX02 • X2
p0 = by-assoc-and (under (ε) (CCX02 • X2) B157.proved) Eq.refl Eq.refl

p1 : CX01 • CCX01 • CX01 • CCX02 • X2 ≈ CX01 • CCX01 • X2 • CCX02
p1 = by-assoc-and (under (CX01 • CCX01) (ε) B130.proved) Eq.refl Eq.refl

p2 : CX02 • CCX01 • CCX02 • X2 ≈ CX01 • CCX01 • X2 • CCX02
p2 = trans (sym p0) p1

p3 : CX02 • CCX01 • CCX02 • X2 ≈ CX02 • CCX01 • CCX02 • X2
p3 = refl

p4 : CX01 • CCX01 • X2 • CCX02 ≈ CX01 • X2 • CCX01 • CCX02
p4 = by-assoc-and (under (CX01) (CCX02) B29.proved) Eq.refl Eq.refl

p5 : CX01 • X2 • CCX01 • CCX02 ≈ X2 • CX01 • CCX01 • CCX02
p5 = by-assoc-and (under (ε) (CCX01 • CCX02) B22.proved) Eq.refl Eq.refl

p6 : CX01 • CCX01 • X2 • CCX02 ≈ X2 • CX01 • CCX01 • CCX02
p6 = trans p4 (trans p5 (refl))

p7 : CX02 • CCX01 • CCX02 • X2 ≈ X2 • CX01 • CCX01 • CCX02
p7 = trans (sym p3) (trans p2 p6)

proved : CX02 • CCX01 • CCX02 • X2 ≈ X2 • CX01 • CCX01 • CCX02
proved = p7
