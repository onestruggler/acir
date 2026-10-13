{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB3229 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0025 as B25
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0212 as B212
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0218 as B218
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0339 as B339
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB3166 as B3166

p0 : CCX12 • CCX01 • CCX12 • CX01 • CCX12 ≈ CCX12 • CCX01 • CX01 • CCX12 • CCX02
p0 = by-assoc-and (under (CCX12 • CCX01) (ε) B339.proved) Eq.refl Eq.refl

p1 : CCX12 • CCX01 • CCX12 • CX01 • CCX12 ≈ CX20 • CCX01 • CX20 • CX01 • CCX12
p1 = by-assoc-and (under (ε) (CX01 • CCX12) B212.proved) Eq.refl Eq.refl

p2 : CCX12 • CCX01 • CX01 • CCX12 • CCX02 ≈ CX20 • CCX01 • CX20 • CX01 • CCX12
p2 = trans (sym p0) p1

p3 : CCX12 • CCX01 • CX01 • CCX12 • CCX02 ≈ CCX02 • CCX12 • CCX01 • CX01 • CCX02
p3 = by-assoc-and (under (ε) (CCX02) B3166.proved) Eq.refl Eq.refl

p4 : CCX12 • CCX01 • CX01 • CCX12 • CCX02 ≈ CCX02 • CCX12 • CCX01 • CX01 • CCX02
p4 = trans p3 (refl)

p5 : CX20 • CCX01 • CX20 • CX01 • CCX12 ≈ CX02 • CCX12 • CX02 • CX01 • CCX12
p5 = by-assoc-and (under (ε) (CX01 • CCX12) B218.proved) Eq.refl Eq.refl

p6 : CX02 • CCX12 • CX02 • CX01 • CCX12 ≈ CX02 • CCX12 • CX01 • CX02 • CCX12
p6 = by-assoc-and (under (CX02 • CCX12) (CCX12) B25.proved) Eq.refl Eq.refl

p7 : CX20 • CCX01 • CX20 • CX01 • CCX12 ≈ CX02 • CCX12 • CX01 • CX02 • CCX12
p7 = trans p5 (trans p6 (refl))

p8 : CCX02 • CCX12 • CCX01 • CX01 • CCX02 ≈ CX02 • CCX12 • CX01 • CX02 • CCX12
p8 = trans (sym p4) (trans p2 p7)

proved : CCX02 • CCX12 • CCX01 • CX01 • CCX02 ≈ CX02 • CCX12 • CX01 • CX02 • CCX12
proved = p8
