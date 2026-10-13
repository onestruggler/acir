{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0445 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0015 as B15
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0061 as B61
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0107 as B107
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0140 as B140

p0 : SWAP12 • CX12 • CCX01 • X0 ≈ SWAP12 • X0 • CCX01
p0 = by-assoc-and (under (SWAP12) (ε) B140.proved) Eq.refl Eq.refl

p1 : SWAP12 • CX12 • CCX01 • X0 ≈ CX12 • CX21 • CCX01 • X0
p1 = by-assoc-and (under (ε) (CCX01 • X0) B61.proved) Eq.refl Eq.refl

p2 : SWAP12 • X0 • CCX01 ≈ CX12 • CX21 • CCX01 • X0
p2 = trans (sym p0) p1

p3 : SWAP12 • X0 • CCX01 ≈ X0 • SWAP12 • CCX01
p3 = by-assoc-and (under (ε) (CCX01) B15.proved) Eq.refl Eq.refl

p4 : X0 • SWAP12 • CCX01 ≈ X0 • CCX02 • SWAP12
p4 = by-assoc-and (under (X0) (ε) B107.proved) Eq.refl Eq.refl

p5 : SWAP12 • X0 • CCX01 ≈ X0 • CCX02 • SWAP12
p5 = trans p3 (trans p4 (refl))

p6 : CX12 • CX21 • CCX01 • X0 ≈ CX12 • CX21 • CCX01 • X0
p6 = refl

p7 : X0 • CCX02 • SWAP12 ≈ CX12 • CX21 • CCX01 • X0
p7 = trans (sym p5) (trans p2 p6)

p8 : CX12 • CX21 • CCX01 • X0 ≈ X0 • CCX02 • SWAP12
p8 = sym p7

proved : CX12 • CX21 • CCX01 • X0 ≈ X0 • CCX02 • SWAP12
proved = p8
