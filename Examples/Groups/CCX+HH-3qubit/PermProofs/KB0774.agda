{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0774 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0028 as B28
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0034 as B34
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0132 as B132
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0136 as B136

p0 : CX21 • CCX02 • CX20 • CCX12 • X1 ≈ CX20 • CCX02 • CCX12 • X1
p0 = by-assoc-and (under (ε) (CCX12 • X1) B136.proved) Eq.refl Eq.refl

p1 : CX21 • CCX02 • CX20 • CCX12 • X1 ≈ CX21 • CCX02 • X1 • CCX12
p1 = by-assoc-and (under (CX21 • CCX02) (ε) B132.proved) Eq.refl Eq.refl

p2 : CX20 • CCX02 • CCX12 • X1 ≈ CX21 • CCX02 • X1 • CCX12
p2 = trans (sym p0) p1

p3 : CX20 • CCX02 • CCX12 • X1 ≈ CX20 • CCX02 • CCX12 • X1
p3 = refl

p4 : CX21 • CCX02 • X1 • CCX12 ≈ CX21 • X1 • CCX02 • CCX12
p4 = by-assoc-and (under (CX21) (CCX12) B28.proved) Eq.refl Eq.refl

p5 : CX21 • X1 • CCX02 • CCX12 ≈ X1 • CX21 • CCX02 • CCX12
p5 = by-assoc-and (under (ε) (CCX02 • CCX12) B34.proved) Eq.refl Eq.refl

p6 : CX21 • CCX02 • X1 • CCX12 ≈ X1 • CX21 • CCX02 • CCX12
p6 = trans p4 (trans p5 (refl))

p7 : CX20 • CCX02 • CCX12 • X1 ≈ X1 • CX21 • CCX02 • CCX12
p7 = trans (sym p3) (trans p2 p6)

proved : CX20 • CCX02 • CCX12 • X1 ≈ X1 • CX21 • CCX02 • CCX12
proved = p7
