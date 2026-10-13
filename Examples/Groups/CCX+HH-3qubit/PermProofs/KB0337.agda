{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0337 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0005 as B5
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0032 as B32
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0335 as B335

p0 : CX10 • CCX12 • CCX02 • CX10 • CX10 ≈ CCX02 • CCX12 • CX10
p0 = by-assoc-and (under (ε) (CX10) B335.proved) Eq.refl Eq.refl

p1 : CX10 • CCX12 • CCX02 • CX10 • CX10 ≈ CX10 • CCX12 • CCX02
p1 = by-assoc-and (under (CX10 • CCX12 • CCX02) (ε) B5.proved) Eq.refl Eq.refl

p2 : CCX02 • CCX12 • CX10 ≈ CX10 • CCX12 • CCX02
p2 = trans (sym p0) p1

p3 : CCX02 • CCX12 • CX10 ≈ CCX02 • CX10 • CCX12
p3 = by-assoc-and (under (CCX02) (ε) B32.proved) Eq.refl Eq.refl

p4 : CCX02 • CCX12 • CX10 ≈ CCX02 • CX10 • CCX12
p4 = trans p3 (refl)

p5 : CX10 • CCX12 • CCX02 ≈ CX10 • CCX12 • CCX02
p5 = refl

p6 : CCX02 • CX10 • CCX12 ≈ CX10 • CCX12 • CCX02
p6 = trans (sym p4) (trans p2 p5)

proved : CCX02 • CX10 • CCX12 ≈ CX10 • CCX12 • CCX02
proved = p6
