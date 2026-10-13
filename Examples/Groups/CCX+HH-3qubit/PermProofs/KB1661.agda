{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1661 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0025 as B25
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0027 as B27
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0088 as B88
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0101 as B101
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0102 as B102
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0164 as B164
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0261 as B261
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0285 as B285
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0311 as B311

p0 : CX10 • CX02 • CX12 • CCX02 • CX02 ≈ CX02 • CX10 • CCX02 • CX02
p0 = by-assoc-and (under (ε) (CCX02 • CX02) B311.proved) Eq.refl Eq.refl

p1 : CX10 • CX02 • CX12 • CCX02 • CX02 ≈ CX10 • CX02 • CX01 • CX12 • CCX02
p1 = by-assoc-and (under (CX10 • CX02) (ε) B285.proved) Eq.refl Eq.refl

p2 : CX02 • CX10 • CCX02 • CX02 ≈ CX10 • CX02 • CX01 • CX12 • CCX02
p2 = trans (sym p0) p1

p3 : CX02 • CX10 • CCX02 • CX02 ≈ CX02 • CX10 • CCX02 • CX02
p3 = refl

p4 : CX10 • CX02 • CX01 • CX12 • CCX02 ≈ CX10 • CX01 • CX02 • CX12 • CCX02
p4 = by-assoc-and (under (CX10) (CX12 • CCX02) B25.proved) Eq.refl Eq.refl

p5 : CX10 • CX01 • CX02 • CX12 • CCX02 ≈ CX01 • SWAP01 • CX02 • CX12 • CCX02
p5 = by-assoc-and (under (ε) (CX02 • CX12 • CCX02) B88.proved) Eq.refl Eq.refl

p6 : CX01 • SWAP01 • CX02 • CX12 • CCX02 ≈ CX01 • CX12 • SWAP01 • CX12 • CCX02
p6 = by-assoc-and (under (CX01) (CX12 • CCX02) B102.proved) Eq.refl Eq.refl

p7 : CX01 • CX12 • SWAP01 • CX12 • CCX02 ≈ CX01 • CX12 • CX02 • SWAP01 • CCX02
p7 = by-assoc-and (under (CX01 • CX12) (CCX02) B101.proved) Eq.refl Eq.refl

p8 : CX01 • CX12 • CX02 • SWAP01 • CCX02 ≈ CX01 • CX02 • CX12 • SWAP01 • CCX02
p8 = by-assoc-and (under (CX01) (SWAP01 • CCX02) B27.proved) Eq.refl Eq.refl

p9 : CX01 • CX02 • CX12 • SWAP01 • CCX02 ≈ CX12 • CX01 • SWAP01 • CCX02
p9 = by-assoc-and (under (ε) (SWAP01 • CCX02) B164.proved) Eq.refl Eq.refl

p10 : CX12 • CX01 • SWAP01 • CCX02 ≈ CX10 • CX12 • CX01 • CCX02
p10 = by-assoc-and (under (ε) (CCX02) B261.proved) Eq.refl Eq.refl

p11 : CX10 • CX02 • CX01 • CX12 • CCX02 ≈ CX10 • CX12 • CX01 • CCX02
p11 = trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (refl)))))))

p12 : CX02 • CX10 • CCX02 • CX02 ≈ CX10 • CX12 • CX01 • CCX02
p12 = trans (sym p3) (trans p2 p11)

p13 : CX10 • CX12 • CX01 • CCX02 ≈ CX02 • CX10 • CCX02 • CX02
p13 = sym p12

proved : CX10 • CX12 • CX01 • CCX02 ≈ CX02 • CX10 • CCX02 • CX02
proved = p13
