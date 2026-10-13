{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0562 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0016 as B16
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0063 as B63
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0090 as B90
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0188 as B188

p0 : SWAP01 • CCX02 • X2 • CX01 ≈ SWAP01 • X2 • CCX02
p0 = by-assoc-and (under (SWAP01) (ε) B188.proved) Eq.refl Eq.refl

p1 : SWAP01 • CCX02 • X2 • CX01 ≈ CCX12 • SWAP01 • X2 • CX01
p1 = by-assoc-and (under (ε) (X2 • CX01) B90.proved) Eq.refl Eq.refl

p2 : SWAP01 • X2 • CCX02 ≈ CCX12 • SWAP01 • X2 • CX01
p2 = trans (sym p0) p1

p3 : SWAP01 • X2 • CCX02 ≈ X2 • SWAP01 • CCX02
p3 = by-assoc-and (under (ε) (CCX02) B16.proved) Eq.refl Eq.refl

p4 : X2 • SWAP01 • CCX02 ≈ X2 • CCX12 • SWAP01
p4 = by-assoc-and (under (X2) (ε) B90.proved) Eq.refl Eq.refl

p5 : SWAP01 • X2 • CCX02 ≈ X2 • CCX12 • SWAP01
p5 = trans p3 (trans p4 (refl))

p6 : CCX12 • SWAP01 • X2 • CX01 ≈ CCX12 • X2 • SWAP01 • CX01
p6 = by-assoc-and (under (CCX12) (CX01) B16.proved) Eq.refl Eq.refl

p7 : CCX12 • X2 • SWAP01 • CX01 ≈ CCX12 • X2 • CX01 • CX10
p7 = by-assoc-and (under (CCX12 • X2) (ε) B63.proved) Eq.refl Eq.refl

p8 : CCX12 • SWAP01 • X2 • CX01 ≈ CCX12 • X2 • CX01 • CX10
p8 = trans p6 (trans p7 (refl))

p9 : X2 • CCX12 • SWAP01 ≈ CCX12 • X2 • CX01 • CX10
p9 = trans (sym p5) (trans p2 p8)

p10 : CCX12 • X2 • CX01 • CX10 ≈ X2 • CCX12 • SWAP01
p10 = sym p9

proved : CCX12 • X2 • CX01 • CX10 ≈ X2 • CCX12 • SWAP01
proved = p10
