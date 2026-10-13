{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0631 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0032 as B32
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0311 as B311
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0447 as B447

p0 : CCX12 • CX10 • CX02 • CX12 ≈ CCX12 • CX02 • CX10
p0 = by-assoc-and (under (CCX12) (ε) B311.proved) Eq.refl Eq.refl

p1 : CCX12 • CX10 • CX02 • CX12 ≈ CX10 • CCX12 • CX02 • CX12
p1 = by-assoc-and (under (ε) (CX02 • CX12) B32.proved) Eq.refl Eq.refl

p2 : CCX12 • CX02 • CX10 ≈ CX10 • CCX12 • CX02 • CX12
p2 = trans (sym p0) p1

p3 : CCX12 • CX02 • CX10 ≈ CCX12 • CX02 • CX10
p3 = refl

p4 : CX10 • CCX12 • CX02 • CX12 ≈ CX12 • CCX12 • CX02
p4 = by-assoc-and (under (ε) (ε) B447.proved) Eq.refl Eq.refl

p5 : CX10 • CCX12 • CX02 • CX12 ≈ CX12 • CCX12 • CX02
p5 = trans p4 (refl)

p6 : CCX12 • CX02 • CX10 ≈ CX12 • CCX12 • CX02
p6 = trans (sym p3) (trans p2 p5)

proved : CCX12 • CX02 • CX10 ≈ CX12 • CCX12 • CX02
proved = p6
