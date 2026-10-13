{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB4012 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0155 as B155
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0663 as B663

p0 : CCX02 • X2 • CCX02 • CX20 • CCX01 • CX21 ≈ CCX02 • X2 • CX20 • CCX01 • CCX02
p0 = by-assoc-and (under (CCX02 • X2) (ε) B663.proved) Eq.refl Eq.refl

p1 : CCX02 • X2 • CCX02 • CX20 • CCX01 • CX21 ≈ X2 • CX01 • CX20 • CCX01 • CX21
p1 = by-assoc-and (under (ε) (CX20 • CCX01 • CX21) B155.proved) Eq.refl Eq.refl

p2 : CCX02 • X2 • CX20 • CCX01 • CCX02 ≈ X2 • CX01 • CX20 • CCX01 • CX21
p2 = trans (sym p0) p1

p3 : CCX02 • X2 • CX20 • CCX01 • CCX02 ≈ CCX02 • X2 • CX20 • CCX01 • CCX02
p3 = refl

p4 : X2 • CX01 • CX20 • CCX01 • CX21 ≈ X2 • CX01 • CX20 • CCX01 • CX21
p4 = refl

p5 : CCX02 • X2 • CX20 • CCX01 • CCX02 ≈ X2 • CX01 • CX20 • CCX01 • CX21
p5 = trans (sym p3) (trans p2 p4)

proved : CCX02 • X2 • CX20 • CCX01 • CCX02 ≈ X2 • CX01 • CX20 • CCX01 • CX21
proved = p5
