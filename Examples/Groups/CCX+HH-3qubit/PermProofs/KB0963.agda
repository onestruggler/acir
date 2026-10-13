{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0963 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0029 as B29
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0036 as B36
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0214 as B214

p0 : CCX01 • CCX02 • CCX01 • X2 ≈ CX12 • CCX02 • CX12 • X2
p0 = by-assoc-and (under (ε) (X2) B214.proved) Eq.refl Eq.refl

p1 : CCX01 • CCX02 • CCX01 • X2 ≈ CCX01 • CCX02 • X2 • CCX01
p1 = by-assoc-and (under (CCX01 • CCX02) (ε) B29.proved) Eq.refl Eq.refl

p2 : CX12 • CCX02 • CX12 • X2 ≈ CCX01 • CCX02 • X2 • CCX01
p2 = trans (sym p0) p1

p3 : CX12 • CCX02 • CX12 • X2 ≈ CX12 • CCX02 • X2 • CX12
p3 = by-assoc-and (under (CX12 • CCX02) (ε) B36.proved) Eq.refl Eq.refl

p4 : CX12 • CCX02 • CX12 • X2 ≈ CX12 • CCX02 • X2 • CX12
p4 = trans p3 (refl)

p5 : CCX01 • CCX02 • X2 • CCX01 ≈ CCX01 • CCX02 • X2 • CCX01
p5 = refl

p6 : CX12 • CCX02 • X2 • CX12 ≈ CCX01 • CCX02 • X2 • CCX01
p6 = trans (sym p4) (trans p2 p5)

p7 : CCX01 • CCX02 • X2 • CCX01 ≈ CX12 • CCX02 • X2 • CX12
p7 = sym p6

proved : CCX01 • CCX02 • X2 • CCX01 ≈ CX12 • CCX02 • X2 • CX12
proved = p7
