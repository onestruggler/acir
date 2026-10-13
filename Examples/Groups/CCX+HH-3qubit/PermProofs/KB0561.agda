{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0561 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0015 as B15
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0061 as B61
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0107 as B107
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0187 as B187

p0 : SWAP12 • CCX01 • X0 • CX12 ≈ SWAP12 • X0 • CCX01
p0 = by-assoc-and (under (SWAP12) (ε) B187.proved) Eq.refl Eq.refl

p1 : SWAP12 • CCX01 • X0 • CX12 ≈ CCX02 • SWAP12 • X0 • CX12
p1 = by-assoc-and (under (ε) (X0 • CX12) B107.proved) Eq.refl Eq.refl

p2 : SWAP12 • X0 • CCX01 ≈ CCX02 • SWAP12 • X0 • CX12
p2 = trans (sym p0) p1

p3 : SWAP12 • X0 • CCX01 ≈ X0 • SWAP12 • CCX01
p3 = by-assoc-and (under (ε) (CCX01) B15.proved) Eq.refl Eq.refl

p4 : X0 • SWAP12 • CCX01 ≈ X0 • CCX02 • SWAP12
p4 = by-assoc-and (under (X0) (ε) B107.proved) Eq.refl Eq.refl

p5 : SWAP12 • X0 • CCX01 ≈ X0 • CCX02 • SWAP12
p5 = trans p3 (trans p4 (refl))

p6 : CCX02 • SWAP12 • X0 • CX12 ≈ CCX02 • X0 • SWAP12 • CX12
p6 = by-assoc-and (under (CCX02) (CX12) B15.proved) Eq.refl Eq.refl

p7 : CCX02 • X0 • SWAP12 • CX12 ≈ CCX02 • X0 • CX12 • CX21
p7 = by-assoc-and (under (CCX02 • X0) (ε) B61.proved) Eq.refl Eq.refl

p8 : CCX02 • SWAP12 • X0 • CX12 ≈ CCX02 • X0 • CX12 • CX21
p8 = trans p6 (trans p7 (refl))

p9 : X0 • CCX02 • SWAP12 ≈ CCX02 • X0 • CX12 • CX21
p9 = trans (sym p5) (trans p2 p8)

p10 : CCX02 • X0 • CX12 • CX21 ≈ X0 • CCX02 • SWAP12
p10 = sym p9

proved : CCX02 • X0 • CX12 • CX21 ≈ X0 • CCX02 • SWAP12
proved = p10
