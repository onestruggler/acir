{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0252 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0036 as B36
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0055 as B55
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0080 as B80

p0 : CX21 • CX12 • X2 ≈ CX12 • SWAP12 • X2
p0 = by-assoc-and (under (ε) (X2) B80.proved) Eq.refl Eq.refl

p1 : CX21 • CX12 • X2 ≈ CX21 • X2 • CX12
p1 = by-assoc-and (under (CX21) (ε) B36.proved) Eq.refl Eq.refl

p2 : CX12 • SWAP12 • X2 ≈ CX21 • X2 • CX12
p2 = trans (sym p0) p1

p3 : CX12 • SWAP12 • X2 ≈ CX12 • X1 • SWAP12
p3 = by-assoc-and (under (CX12) (ε) B55.proved) Eq.refl Eq.refl

p4 : CX12 • SWAP12 • X2 ≈ CX12 • X1 • SWAP12
p4 = trans p3 (refl)

p5 : CX21 • X2 • CX12 ≈ CX21 • X2 • CX12
p5 = refl

p6 : CX12 • X1 • SWAP12 ≈ CX21 • X2 • CX12
p6 = trans (sym p4) (trans p2 p5)

p7 : CX21 • X2 • CX12 ≈ CX12 • X1 • SWAP12
p7 = sym p6

proved : CX21 • X2 • CX12 ≈ CX12 • X1 • SWAP12
proved = p7
