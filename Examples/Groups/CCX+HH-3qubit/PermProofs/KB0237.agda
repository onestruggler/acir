{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0237 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0026 as B26
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0061 as B61
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0072 as B72

p0 : SWAP12 • CX12 • CX10 ≈ CX12 • CX21 • CX10
p0 = by-assoc-and (under (ε) (CX10) B61.proved) Eq.refl Eq.refl

p1 : SWAP12 • CX12 • CX10 ≈ SWAP12 • CX10 • CX12
p1 = by-assoc-and (under (SWAP12) (ε) B26.proved) Eq.refl Eq.refl

p2 : CX12 • CX21 • CX10 ≈ SWAP12 • CX10 • CX12
p2 = trans (sym p0) p1

p3 : CX12 • CX21 • CX10 ≈ CX12 • CX21 • CX10
p3 = refl

p4 : SWAP12 • CX10 • CX12 ≈ CX20 • SWAP12 • CX12
p4 = by-assoc-and (under (ε) (CX12) B72.proved) Eq.refl Eq.refl

p5 : CX20 • SWAP12 • CX12 ≈ CX20 • CX12 • CX21
p5 = by-assoc-and (under (CX20) (ε) B61.proved) Eq.refl Eq.refl

p6 : SWAP12 • CX10 • CX12 ≈ CX20 • CX12 • CX21
p6 = trans p4 (trans p5 (refl))

p7 : CX12 • CX21 • CX10 ≈ CX20 • CX12 • CX21
p7 = trans (sym p3) (trans p2 p6)

p8 : CX20 • CX12 • CX21 ≈ CX12 • CX21 • CX10
p8 = sym p7

proved : CX20 • CX12 • CX21 ≈ CX12 • CX21 • CX10
proved = p8
