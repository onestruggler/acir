{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0226 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0039 as B39
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0041 as B41

p0 : CCX02 • CX21 • SWAP12 ≈ CCX02 • CX12 • CX21
p0 = by-assoc-and (under (CCX02) (ε) B41.proved) Eq.refl Eq.refl

p1 : CCX02 • CX21 • SWAP12 ≈ CX21 • CCX02 • SWAP12
p1 = by-assoc-and (under (ε) (SWAP12) B39.proved) Eq.refl Eq.refl

p2 : CCX02 • CX12 • CX21 ≈ CX21 • CCX02 • SWAP12
p2 = trans (sym p0) p1

p3 : CCX02 • CX12 • CX21 ≈ CCX02 • CX12 • CX21
p3 = refl

p4 : CX21 • CCX02 • SWAP12 ≈ CX21 • CCX02 • SWAP12
p4 = refl

p5 : CCX02 • CX12 • CX21 ≈ CX21 • CCX02 • SWAP12
p5 = trans (sym p3) (trans p2 p4)

proved : CCX02 • CX12 • CX21 ≈ CX21 • CCX02 • SWAP12
proved = p5
