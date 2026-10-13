{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1276 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0013 as B13
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0216 as B216
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0228 as B228
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0264 as B264
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0336 as B336

p0 : CCX02 • CCX12 • CCX02 • CX10 ≈ CCX02 • CX10 • CCX02 • CCX12
p0 = by-assoc-and (under (CCX02) (ε) B336.proved) Eq.refl Eq.refl

p1 : CCX02 • CCX12 • CCX02 • CX10 ≈ CX01 • CCX12 • CX01 • CX10
p1 = by-assoc-and (under (ε) (CX10) B216.proved) Eq.refl Eq.refl

p2 : CCX02 • CX10 • CCX02 • CCX12 ≈ CX01 • CCX12 • CX01 • CX10
p2 = trans (sym p0) p1

p3 : CCX02 • CX10 • CCX02 • CCX12 ≈ CCX02 • CX10 • CCX02 • CCX12
p3 = refl

p4 : CX01 • CCX12 • CX01 • CX10 ≈ CX01 • CX10 • CCX12 • SWAP01
p4 = by-assoc-and (under (CX01) (ε) B228.proved) Eq.refl Eq.refl

p5 : CX01 • CX10 • CCX12 • SWAP01 ≈ CX01 • CX01 • CX10 • CCX02
p5 = by-assoc-and (under (CX01) (ε) B264.proved) Eq.refl Eq.refl

p6 : CX01 • CX01 • CX10 • CCX02 ≈ CX10 • CCX02
p6 = by-assoc-and (under (ε) (CX10 • CCX02) B13.proved) Eq.refl Eq.refl

p7 : CX01 • CCX12 • CX01 • CX10 ≈ CX10 • CCX02
p7 = trans p4 (trans p5 (trans p6 (refl)))

p8 : CCX02 • CX10 • CCX02 • CCX12 ≈ CX10 • CCX02
p8 = trans (sym p3) (trans p2 p7)

proved : CCX02 • CX10 • CCX02 • CCX12 ≈ CX10 • CCX02
proved = p8
