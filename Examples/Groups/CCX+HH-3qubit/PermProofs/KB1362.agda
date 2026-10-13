{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1362 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0026 as B26
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0180 as B180
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0335 as B335

p0 : CX12 • CX10 • CCX12 • CCX02 • CX10 ≈ CX12 • CCX02 • CCX12
p0 = by-assoc-and (under (CX12) (ε) B335.proved) Eq.refl Eq.refl

p1 : CX12 • CX10 • CCX12 • CCX02 • CX10 ≈ CX10 • CX12 • CCX12 • CCX02 • CX10
p1 = by-assoc-and (under (ε) (CCX12 • CCX02 • CX10) B26.proved) Eq.refl Eq.refl

p2 : CX12 • CCX02 • CCX12 ≈ CX10 • CX12 • CCX12 • CCX02 • CX10
p2 = trans (sym p0) p1

p3 : CX12 • CCX02 • CCX12 ≈ CX12 • CCX02 • CCX12
p3 = refl

p4 : CX10 • CX12 • CCX12 • CCX02 • CX10 ≈ CCX12 • CX12 • CCX02 • CX10
p4 = by-assoc-and (under (ε) (CCX02 • CX10) B180.proved) Eq.refl Eq.refl

p5 : CX10 • CX12 • CCX12 • CCX02 • CX10 ≈ CCX12 • CX12 • CCX02 • CX10
p5 = trans p4 (refl)

p6 : CX12 • CCX02 • CCX12 ≈ CCX12 • CX12 • CCX02 • CX10
p6 = trans (sym p3) (trans p2 p5)

p7 : CCX12 • CX12 • CCX02 • CX10 ≈ CX12 • CCX02 • CCX12
p7 = sym p6

proved : CCX12 • CX12 • CCX02 • CX10 ≈ CX12 • CCX02 • CCX12
proved = p7
