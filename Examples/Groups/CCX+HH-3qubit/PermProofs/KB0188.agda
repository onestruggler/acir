{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0188 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0010 as B10
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0155 as B155

p0 : CCX02 • CCX02 • X2 • CCX02 ≈ CCX02 • X2 • CX01
p0 = by-assoc-and (under (CCX02) (ε) B155.proved) Eq.refl Eq.refl

p1 : CCX02 • CCX02 • X2 • CCX02 ≈ X2 • CCX02
p1 = by-assoc-and (under (ε) (X2 • CCX02) B10.proved) Eq.refl Eq.refl

p2 : CCX02 • X2 • CX01 ≈ X2 • CCX02
p2 = trans (sym p0) p1

p3 : CCX02 • X2 • CX01 ≈ CCX02 • X2 • CX01
p3 = refl

p4 : X2 • CCX02 ≈ X2 • CCX02
p4 = refl

p5 : CCX02 • X2 • CX01 ≈ X2 • CCX02
p5 = trans (sym p3) (trans p2 p4)

proved : CCX02 • X2 • CX01 ≈ X2 • CCX02
proved = p5
