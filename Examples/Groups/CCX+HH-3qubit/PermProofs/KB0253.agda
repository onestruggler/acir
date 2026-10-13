{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0253 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0039 as B39
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0080 as B80

p0 : CCX02 • CX21 • CX12 ≈ CCX02 • CX12 • SWAP12
p0 = by-assoc-and (under (CCX02) (ε) B80.proved) Eq.refl Eq.refl

p1 : CCX02 • CX21 • CX12 ≈ CX21 • CCX02 • CX12
p1 = by-assoc-and (under (ε) (CX12) B39.proved) Eq.refl Eq.refl

p2 : CCX02 • CX12 • SWAP12 ≈ CX21 • CCX02 • CX12
p2 = trans (sym p0) p1

p3 : CCX02 • CX12 • SWAP12 ≈ CCX02 • CX12 • SWAP12
p3 = refl

p4 : CX21 • CCX02 • CX12 ≈ CX21 • CCX02 • CX12
p4 = refl

p5 : CCX02 • CX12 • SWAP12 ≈ CX21 • CCX02 • CX12
p5 = trans (sym p3) (trans p2 p4)

proved : CCX02 • CX12 • SWAP12 ≈ CX21 • CCX02 • CX12
proved = p5
