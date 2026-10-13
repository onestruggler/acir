{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB3166 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0013 as B13
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1761 as B1761
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB3165 as B3165

p0 : CX01 • CX01 • CCX12 • CCX01 • CX01 • CCX12 ≈ CX01 • CCX12 • CCX02 • CX02 • CCX01
p0 = by-assoc-and (under (CX01) (ε) B3165.proved) Eq.refl Eq.refl

p1 : CX01 • CX01 • CCX12 • CCX01 • CX01 • CCX12 ≈ CCX12 • CCX01 • CX01 • CCX12
p1 = by-assoc-and (under (ε) (CCX12 • CCX01 • CX01 • CCX12) B13.proved) Eq.refl Eq.refl

p2 : CX01 • CCX12 • CCX02 • CX02 • CCX01 ≈ CCX12 • CCX01 • CX01 • CCX12
p2 = trans (sym p0) p1

p3 : CX01 • CCX12 • CCX02 • CX02 • CCX01 ≈ CCX02 • CCX12 • CCX01 • CX01
p3 = by-assoc-and (under (ε) (ε) B1761.proved) Eq.refl Eq.refl

p4 : CX01 • CCX12 • CCX02 • CX02 • CCX01 ≈ CCX02 • CCX12 • CCX01 • CX01
p4 = trans p3 (refl)

p5 : CCX12 • CCX01 • CX01 • CCX12 ≈ CCX12 • CCX01 • CX01 • CCX12
p5 = refl

p6 : CCX02 • CCX12 • CCX01 • CX01 ≈ CCX12 • CCX01 • CX01 • CCX12
p6 = trans (sym p4) (trans p2 p5)

p7 : CCX12 • CCX01 • CX01 • CCX12 ≈ CCX02 • CCX12 • CCX01 • CX01
p7 = sym p6

proved : CCX12 • CCX01 • CX01 • CCX12 ≈ CCX02 • CCX12 • CCX01 • CX01
proved = p7
