{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1265 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0006 as B6
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0214 as B214
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0226 as B226
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0278 as B278
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0329 as B329

p0 : CCX01 • CCX02 • CCX01 • CX21 ≈ CCX01 • CX21 • CCX01 • CCX02
p0 = by-assoc-and (under (CCX01) (ε) B329.proved) Eq.refl Eq.refl

p1 : CCX01 • CCX02 • CCX01 • CX21 ≈ CX12 • CCX02 • CX12 • CX21
p1 = by-assoc-and (under (ε) (CX21) B214.proved) Eq.refl Eq.refl

p2 : CCX01 • CX21 • CCX01 • CCX02 ≈ CX12 • CCX02 • CX12 • CX21
p2 = trans (sym p0) p1

p3 : CCX01 • CX21 • CCX01 • CCX02 ≈ CCX01 • CX21 • CCX01 • CCX02
p3 = refl

p4 : CX12 • CCX02 • CX12 • CX21 ≈ CX12 • CX21 • CCX02 • SWAP12
p4 = by-assoc-and (under (CX12) (ε) B226.proved) Eq.refl Eq.refl

p5 : CX12 • CX21 • CCX02 • SWAP12 ≈ CX12 • CX12 • CX21 • CCX01
p5 = by-assoc-and (under (CX12) (ε) B278.proved) Eq.refl Eq.refl

p6 : CX12 • CX12 • CX21 • CCX01 ≈ CX21 • CCX01
p6 = by-assoc-and (under (ε) (CX21 • CCX01) B6.proved) Eq.refl Eq.refl

p7 : CX12 • CCX02 • CX12 • CX21 ≈ CX21 • CCX01
p7 = trans p4 (trans p5 (trans p6 (refl)))

p8 : CCX01 • CX21 • CCX01 • CCX02 ≈ CX21 • CCX01
p8 = trans (sym p3) (trans p2 p7)

proved : CCX01 • CX21 • CCX01 • CCX02 ≈ CX21 • CCX01
proved = p8
