{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0166 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0012 as B12
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0129 as B129

p0 : CX21 • CCX02 • X0 • X0 ≈ X0 • CCX02 • X0
p0 = by-assoc-and (under (ε) (X0) B129.proved) Eq.refl Eq.refl

p1 : CX21 • CCX02 • X0 • X0 ≈ CX21 • CCX02
p1 = by-assoc-and (under (CX21 • CCX02) (ε) B12.proved) Eq.refl Eq.refl

p2 : X0 • CCX02 • X0 ≈ CX21 • CCX02
p2 = trans (sym p0) p1

p3 : X0 • CCX02 • X0 ≈ X0 • CCX02 • X0
p3 = refl

p4 : CX21 • CCX02 ≈ CX21 • CCX02
p4 = refl

p5 : X0 • CCX02 • X0 ≈ CX21 • CCX02
p5 = trans (sym p3) (trans p2 p4)

proved : X0 • CCX02 • X0 ≈ CX21 • CCX02
proved = p5
