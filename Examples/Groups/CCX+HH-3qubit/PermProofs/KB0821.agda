{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0821 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0088 as B88
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0090 as B90
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0091 as B91
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0131 as B131
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0154 as B154
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0342 as B342

p0 : CX10 • CCX12 • X2 • CCX02 • X2 ≈ CX10 • CCX12 • CX01 • CCX02
p0 = by-assoc-and (under (CX10 • CCX12) (ε) B154.proved) Eq.refl Eq.refl

p1 : CX10 • CCX12 • X2 • CCX02 • X2 ≈ X2 • CCX12 • CCX02 • X2
p1 = by-assoc-and (under (ε) (CCX02 • X2) B131.proved) Eq.refl Eq.refl

p2 : CX10 • CCX12 • CX01 • CCX02 ≈ X2 • CCX12 • CCX02 • X2
p2 = trans (sym p0) p1

p3 : CX10 • CCX12 • CX01 • CCX02 ≈ CX10 • CX01 • CCX02 • CCX12
p3 = by-assoc-and (under (CX10) (ε) B342.proved) Eq.refl Eq.refl

p4 : CX10 • CX01 • CCX02 • CCX12 ≈ CX01 • SWAP01 • CCX02 • CCX12
p4 = by-assoc-and (under (ε) (CCX02 • CCX12) B88.proved) Eq.refl Eq.refl

p5 : CX01 • SWAP01 • CCX02 • CCX12 ≈ CX01 • CCX12 • SWAP01 • CCX12
p5 = by-assoc-and (under (CX01) (CCX12) B90.proved) Eq.refl Eq.refl

p6 : CX01 • CCX12 • SWAP01 • CCX12 ≈ CX01 • CCX12 • CCX02 • SWAP01
p6 = by-assoc-and (under (CX01 • CCX12) (ε) B91.proved) Eq.refl Eq.refl

p7 : CX10 • CCX12 • CX01 • CCX02 ≈ CX01 • CCX12 • CCX02 • SWAP01
p7 = trans p3 (trans p4 (trans p5 (trans p6 (refl))))

p8 : X2 • CCX12 • CCX02 • X2 ≈ X2 • CCX12 • CCX02 • X2
p8 = refl

p9 : CX01 • CCX12 • CCX02 • SWAP01 ≈ X2 • CCX12 • CCX02 • X2
p9 = trans (sym p7) (trans p2 p8)

proved : CX01 • CCX12 • CCX02 • SWAP01 ≈ X2 • CCX12 • CCX02 • X2
proved = p9
