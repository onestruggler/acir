{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1097 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0037 as B37
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0260 as B260

p0 : CCX01 • CX02 • CX20 • X2 ≈ CCX01 • X0 • CX02 • CX20
p0 = by-assoc-and (under (CCX01) (ε) B260.proved) Eq.refl Eq.refl

p1 : CCX01 • CX02 • CX20 • X2 ≈ CX02 • CCX01 • CX20 • X2
p1 = by-assoc-and (under (ε) (CX20 • X2) B37.proved) Eq.refl Eq.refl

p2 : CCX01 • X0 • CX02 • CX20 ≈ CX02 • CCX01 • CX20 • X2
p2 = trans (sym p0) p1

p3 : CCX01 • X0 • CX02 • CX20 ≈ CCX01 • X0 • CX02 • CX20
p3 = refl

p4 : CX02 • CCX01 • CX20 • X2 ≈ CX02 • CCX01 • CX20 • X2
p4 = refl

p5 : CCX01 • X0 • CX02 • CX20 ≈ CX02 • CCX01 • CX20 • X2
p5 = trans (sym p3) (trans p2 p4)

proved : CCX01 • X0 • CX02 • CX20 ≈ CX02 • CCX01 • CX20 • X2
proved = p5
