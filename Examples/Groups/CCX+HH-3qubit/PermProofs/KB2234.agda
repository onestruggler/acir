{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB2234 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0026 as B26
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0036 as B36
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0486 as B486
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1100 as B1100
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1661 as B1661

p0 : CX12 • X2 • CX10 • CCX02 • X2 ≈ CX12 • CX01 • CCX12 • SWAP01
p0 = by-assoc-and (under (CX12) (ε) B486.proved) Eq.refl Eq.refl

p1 : CX12 • X2 • CX10 • CCX02 • X2 ≈ X2 • CX12 • CX10 • CCX02 • X2
p1 = by-assoc-and (under (ε) (CX10 • CCX02 • X2) B36.proved) Eq.refl Eq.refl

p2 : CX12 • CX01 • CCX12 • SWAP01 ≈ X2 • CX12 • CX10 • CCX02 • X2
p2 = trans (sym p0) p1

p3 : CX12 • CX01 • CCX12 • SWAP01 ≈ CX10 • CX12 • CX01 • CCX02
p3 = by-assoc-and (under (ε) (ε) B1100.proved) Eq.refl Eq.refl

p4 : CX10 • CX12 • CX01 • CCX02 ≈ CX02 • CX10 • CCX02 • CX02
p4 = by-assoc-and (under (ε) (ε) B1661.proved) Eq.refl Eq.refl

p5 : CX12 • CX01 • CCX12 • SWAP01 ≈ CX02 • CX10 • CCX02 • CX02
p5 = trans p3 (trans p4 (refl))

p6 : X2 • CX12 • CX10 • CCX02 • X2 ≈ X2 • CX10 • CX12 • CCX02 • X2
p6 = by-assoc-and (under (X2) (CCX02 • X2) B26.proved) Eq.refl Eq.refl

p7 : X2 • CX12 • CX10 • CCX02 • X2 ≈ X2 • CX10 • CX12 • CCX02 • X2
p7 = trans p6 (refl)

p8 : CX02 • CX10 • CCX02 • CX02 ≈ X2 • CX10 • CX12 • CCX02 • X2
p8 = trans (sym p5) (trans p2 p7)

p9 : X2 • CX10 • CX12 • CCX02 • X2 ≈ CX02 • CX10 • CCX02 • CX02
p9 = sym p8

proved : X2 • CX10 • CX12 • CCX02 • X2 ≈ CX02 • CX10 • CCX02 • CX02
proved = p9
