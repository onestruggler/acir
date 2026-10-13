{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0310 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0057 as B57
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0059 as B59
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0086 as B86
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0175 as B175
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0236 as B236

p0 : SWAP02 • CX12 • SWAP02 • CX02 ≈ SWAP02 • CX12 • CX02 • CX20
p0 = by-assoc-and (under (SWAP02 • CX12) (ε) B86.proved) Eq.refl Eq.refl

p1 : SWAP02 • CX12 • SWAP02 • CX02 ≈ CX10 • CX02
p1 = by-assoc-and (under (ε) (CX02) B57.proved) Eq.refl Eq.refl

p2 : SWAP02 • CX12 • CX02 • CX20 ≈ CX10 • CX02
p2 = trans (sym p0) p1

p3 : SWAP02 • CX12 • CX02 • CX20 ≈ CX10 • SWAP02 • CX02 • CX20
p3 = by-assoc-and (under (ε) (CX02 • CX20) B59.proved) Eq.refl Eq.refl

p4 : CX10 • SWAP02 • CX02 • CX20 ≈ CX10 • CX02 • CX20 • CX20
p4 = by-assoc-and (under (CX10) (CX20) B86.proved) Eq.refl Eq.refl

p5 : CX10 • CX02 • CX20 • CX20 ≈ CX02 • CX20 • CX12 • CX20
p5 = by-assoc-and (under (ε) (CX20) B236.proved) Eq.refl Eq.refl

p6 : CX02 • CX20 • CX12 • CX20 ≈ CX02 • CX10 • CX12
p6 = by-assoc-and (under (CX02) (ε) B175.proved) Eq.refl Eq.refl

p7 : SWAP02 • CX12 • CX02 • CX20 ≈ CX02 • CX10 • CX12
p7 = trans p3 (trans p4 (trans p5 (trans p6 (refl))))

p8 : CX10 • CX02 ≈ CX10 • CX02
p8 = refl

p9 : CX02 • CX10 • CX12 ≈ CX10 • CX02
p9 = trans (sym p7) (trans p2 p8)

proved : CX02 • CX10 • CX12 ≈ CX10 • CX02
proved = p9
