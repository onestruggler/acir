{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1309 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0188 as B188
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0388 as B388
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1277 as B1277

p0 : CCX02 • X2 • CX01 • CX10 • CCX02 ≈ CCX02 • CCX12 • X2 • SWAP01
p0 = by-assoc-and (under (CCX02) (ε) B388.proved) Eq.refl Eq.refl

p1 : CCX02 • X2 • CX01 • CX10 • CCX02 ≈ X2 • CCX02 • CX10 • CCX02
p1 = by-assoc-and (under (ε) (CX10 • CCX02) B188.proved) Eq.refl Eq.refl

p2 : CCX02 • CCX12 • X2 • SWAP01 ≈ X2 • CCX02 • CX10 • CCX02
p2 = trans (sym p0) p1

p3 : CCX02 • CCX12 • X2 • SWAP01 ≈ CCX02 • CCX12 • X2 • SWAP01
p3 = refl

p4 : X2 • CCX02 • CX10 • CCX02 ≈ X2 • CX10 • CCX02 • CCX12
p4 = by-assoc-and (under (X2) (ε) B1277.proved) Eq.refl Eq.refl

p5 : X2 • CCX02 • CX10 • CCX02 ≈ X2 • CX10 • CCX02 • CCX12
p5 = trans p4 (refl)

p6 : CCX02 • CCX12 • X2 • SWAP01 ≈ X2 • CX10 • CCX02 • CCX12
p6 = trans (sym p3) (trans p2 p5)

proved : CCX02 • CCX12 • X2 • SWAP01 ≈ X2 • CX10 • CCX02 • CCX12
proved = p6
