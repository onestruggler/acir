{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0277 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0099 as B99
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0105 as B105

p0 : CX20 • SWAP02 • CCX12 ≈ CX20 • CCX01 • SWAP02
p0 = by-assoc-and (under (CX20) (ε) B105.proved) Eq.refl Eq.refl

p1 : CX20 • SWAP02 • CCX12 ≈ CX02 • CX20 • CCX12
p1 = by-assoc-and (under (ε) (CCX12) B99.proved) Eq.refl Eq.refl

p2 : CX20 • CCX01 • SWAP02 ≈ CX02 • CX20 • CCX12
p2 = trans (sym p0) p1

p3 : CX20 • CCX01 • SWAP02 ≈ CX20 • CCX01 • SWAP02
p3 = refl

p4 : CX02 • CX20 • CCX12 ≈ CX02 • CX20 • CCX12
p4 = refl

p5 : CX20 • CCX01 • SWAP02 ≈ CX02 • CX20 • CCX12
p5 = trans (sym p3) (trans p2 p4)

proved : CX20 • CCX01 • SWAP02 ≈ CX02 • CX20 • CCX12
proved = p5
