{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0232 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0041 as B41
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0049 as B49
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0053 as B53

p0 : CX21 • SWAP12 • SWAP02 ≈ CX21 • SWAP02 • SWAP01
p0 = by-assoc-and (under (CX21) (ε) B49.proved) Eq.refl Eq.refl

p1 : CX21 • SWAP12 • SWAP02 ≈ CX12 • CX21 • SWAP02
p1 = by-assoc-and (under (ε) (SWAP02) B41.proved) Eq.refl Eq.refl

p2 : CX21 • SWAP02 • SWAP01 ≈ CX12 • CX21 • SWAP02
p2 = trans (sym p0) p1

p3 : CX21 • SWAP02 • SWAP01 ≈ CX21 • SWAP01 • SWAP12
p3 = by-assoc-and (under (CX21) (ε) B53.proved) Eq.refl Eq.refl

p4 : CX21 • SWAP02 • SWAP01 ≈ CX21 • SWAP01 • SWAP12
p4 = trans p3 (refl)

p5 : CX12 • CX21 • SWAP02 ≈ CX12 • CX21 • SWAP02
p5 = refl

p6 : CX21 • SWAP01 • SWAP12 ≈ CX12 • CX21 • SWAP02
p6 = trans (sym p4) (trans p2 p5)

proved : CX21 • SWAP01 • SWAP12 ≈ CX12 • CX21 • SWAP02
proved = p6
