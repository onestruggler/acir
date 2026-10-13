{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0165 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0007 as B7
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0020 as B20
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0129 as B129

p0 : CX21 • CX21 • CCX02 • X0 ≈ CX21 • X0 • CCX02
p0 = by-assoc-and (under (CX21) (ε) B129.proved) Eq.refl Eq.refl

p1 : CX21 • CX21 • CCX02 • X0 ≈ CCX02 • X0
p1 = by-assoc-and (under (ε) (CCX02 • X0) B7.proved) Eq.refl Eq.refl

p2 : CX21 • X0 • CCX02 ≈ CCX02 • X0
p2 = trans (sym p0) p1

p3 : CX21 • X0 • CCX02 ≈ X0 • CX21 • CCX02
p3 = by-assoc-and (under (ε) (CCX02) B20.proved) Eq.refl Eq.refl

p4 : CX21 • X0 • CCX02 ≈ X0 • CX21 • CCX02
p4 = trans p3 (refl)

p5 : CCX02 • X0 ≈ CCX02 • X0
p5 = refl

p6 : X0 • CX21 • CCX02 ≈ CCX02 • X0
p6 = trans (sym p4) (trans p2 p5)

proved : X0 • CX21 • CCX02 ≈ CCX02 • X0
proved = p6
