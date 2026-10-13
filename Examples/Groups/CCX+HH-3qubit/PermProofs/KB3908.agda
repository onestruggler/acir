{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB3908 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0037 as B37
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0085 as B85
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0104 as B104
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0105 as B105
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0294 as B294
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0315 as B315
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0322 as B322
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0325 as B325
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0631 as B631
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0811 as B811

p0 : CCX01 • CX20 • CCX12 • CX02 • CX10 ≈ CCX01 • CX20 • CX12 • CCX12 • CX02
p0 = by-assoc-and (under (CCX01 • CX20) (ε) B631.proved) Eq.refl Eq.refl

p1 : CCX01 • CX20 • CCX12 • CX02 • CX10 ≈ CX20 • CCX12 • CCX01 • CX02 • CX10
p1 = by-assoc-and (under (ε) (CX02 • CX10) B325.proved) Eq.refl Eq.refl

p2 : CCX01 • CX20 • CX12 • CCX12 • CX02 ≈ CX20 • CCX12 • CCX01 • CX02 • CX10
p2 = trans (sym p0) p1

p3 : CCX01 • CX20 • CX12 • CCX12 • CX02 ≈ CX10 • CCX01 • CX20 • CCX12 • CX02
p3 = by-assoc-and (under (ε) (CCX12 • CX02) B294.proved) Eq.refl Eq.refl

p4 : CX10 • CCX01 • CX20 • CCX12 • CX02 ≈ CX10 • CX20 • CCX12 • CCX01 • CX02
p4 = by-assoc-and (under (CX10) (CX02) B325.proved) Eq.refl Eq.refl

p5 : CX10 • CX20 • CCX12 • CCX01 • CX02 ≈ CX10 • CX20 • CCX12 • CX02 • CCX01
p5 = by-assoc-and (under (CX10 • CX20 • CCX12) (ε) B37.proved) Eq.refl Eq.refl

p6 : CX10 • CX20 • CCX12 • CX02 • CCX01 ≈ CX10 • CX20 • CX02 • CCX01 • CCX12
p6 = by-assoc-and (under (CX10 • CX20) (ε) B322.proved) Eq.refl Eq.refl

p7 : CX10 • CX20 • CX02 • CCX01 • CCX12 ≈ CX10 • CX02 • SWAP02 • CCX01 • CCX12
p7 = by-assoc-and (under (CX10) (CCX01 • CCX12) B85.proved) Eq.refl Eq.refl

p8 : CX10 • CX02 • SWAP02 • CCX01 • CCX12 ≈ CX10 • CX02 • CCX12 • SWAP02 • CCX12
p8 = by-assoc-and (under (CX10 • CX02) (CCX12) B104.proved) Eq.refl Eq.refl

p9 : CX10 • CX02 • CCX12 • SWAP02 • CCX12 ≈ CX02 • CCX12 • CX12 • SWAP02 • CCX12
p9 = by-assoc-and (under (ε) (SWAP02 • CCX12) B315.proved) Eq.refl Eq.refl

p10 : CX02 • CCX12 • CX12 • SWAP02 • CCX12 ≈ CX02 • CCX12 • CX12 • CCX01 • SWAP02
p10 = by-assoc-and (under (CX02 • CCX12 • CX12) (ε) B105.proved) Eq.refl Eq.refl

p11 : CCX01 • CX20 • CX12 • CCX12 • CX02 ≈ CX02 • CCX12 • CX12 • CCX01 • SWAP02
p11 = trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (refl))))))))

p12 : CX20 • CCX12 • CCX01 • CX02 • CX10 ≈ CX20 • CCX12 • CX02 • CCX01 • CX10
p12 = by-assoc-and (under (CX20 • CCX12) (CX10) B37.proved) Eq.refl Eq.refl

p13 : CX20 • CCX12 • CX02 • CCX01 • CX10 ≈ CX20 • CX02 • CCX01 • CCX12 • CX10
p13 = by-assoc-and (under (CX20) (CX10) B322.proved) Eq.refl Eq.refl

p14 : CX20 • CX02 • CCX01 • CCX12 • CX10 ≈ CX02 • SWAP02 • CCX01 • CCX12 • CX10
p14 = by-assoc-and (under (ε) (CCX01 • CCX12 • CX10) B85.proved) Eq.refl Eq.refl

p15 : CX02 • SWAP02 • CCX01 • CCX12 • CX10 ≈ CX02 • CCX12 • SWAP02 • CCX12 • CX10
p15 = by-assoc-and (under (CX02) (CCX12 • CX10) B104.proved) Eq.refl Eq.refl

p16 : CX02 • CCX12 • SWAP02 • CCX12 • CX10 ≈ CX02 • CCX12 • CCX01 • SWAP02 • CX10
p16 = by-assoc-and (under (CX02 • CCX12) (CX10) B105.proved) Eq.refl Eq.refl

p17 : CX02 • CCX12 • CCX01 • SWAP02 • CX10 ≈ X1 • CCX12 • CCX01 • X1 • CX10
p17 = by-assoc-and (under (ε) (CX10) B811.proved) Eq.refl Eq.refl

p18 : CX20 • CCX12 • CCX01 • CX02 • CX10 ≈ X1 • CCX12 • CCX01 • X1 • CX10
p18 = trans p12 (trans p13 (trans p14 (trans p15 (trans p16 (trans p17 (refl))))))

p19 : CX02 • CCX12 • CX12 • CCX01 • SWAP02 ≈ X1 • CCX12 • CCX01 • X1 • CX10
p19 = trans (sym p11) (trans p2 p18)

proved : CX02 • CCX12 • CX12 • CCX01 • SWAP02 ≈ X1 • CCX12 • CCX01 • X1 • CX10
proved = p19
