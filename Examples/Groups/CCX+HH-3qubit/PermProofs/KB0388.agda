{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0388 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0016 as B16
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0063 as B63
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0090 as B90
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0122 as B122

p0 : SWAP01 • X2 • CX01 • CCX02 ≈ SWAP01 • CCX02 • X2
p0 = by-assoc-and (under (SWAP01) (ε) B122.proved) Eq.refl Eq.refl

p1 : SWAP01 • X2 • CX01 • CCX02 ≈ X2 • SWAP01 • CX01 • CCX02
p1 = by-assoc-and (under (ε) (CX01 • CCX02) B16.proved) Eq.refl Eq.refl

p2 : SWAP01 • CCX02 • X2 ≈ X2 • SWAP01 • CX01 • CCX02
p2 = trans (sym p0) p1

p3 : SWAP01 • CCX02 • X2 ≈ CCX12 • SWAP01 • X2
p3 = by-assoc-and (under (ε) (X2) B90.proved) Eq.refl Eq.refl

p4 : CCX12 • SWAP01 • X2 ≈ CCX12 • X2 • SWAP01
p4 = by-assoc-and (under (CCX12) (ε) B16.proved) Eq.refl Eq.refl

p5 : SWAP01 • CCX02 • X2 ≈ CCX12 • X2 • SWAP01
p5 = trans p3 (trans p4 (refl))

p6 : X2 • SWAP01 • CX01 • CCX02 ≈ X2 • CX01 • CX10 • CCX02
p6 = by-assoc-and (under (X2) (CCX02) B63.proved) Eq.refl Eq.refl

p7 : X2 • SWAP01 • CX01 • CCX02 ≈ X2 • CX01 • CX10 • CCX02
p7 = trans p6 (refl)

p8 : CCX12 • X2 • SWAP01 ≈ X2 • CX01 • CX10 • CCX02
p8 = trans (sym p5) (trans p2 p7)

p9 : X2 • CX01 • CX10 • CCX02 ≈ CCX12 • X2 • SWAP01
p9 = sym p8

proved : X2 • CX01 • CX10 • CCX02 ≈ CCX12 • X2 • SWAP01
proved = p9
