{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0239 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0035 as B35
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0063 as B63
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0096 as B96

p0 : SWAP01 • CX01 • X1 ≈ CX01 • CX10 • X1
p0 = by-assoc-and (under (ε) (X1) B63.proved) Eq.refl Eq.refl

p1 : SWAP01 • CX01 • X1 ≈ SWAP01 • X1 • CX01
p1 = by-assoc-and (under (SWAP01) (ε) B35.proved) Eq.refl Eq.refl

p2 : CX01 • CX10 • X1 ≈ SWAP01 • X1 • CX01
p2 = trans (sym p0) p1

p3 : CX01 • CX10 • X1 ≈ CX01 • CX10 • X1
p3 = refl

p4 : SWAP01 • X1 • CX01 ≈ X0 • SWAP01 • CX01
p4 = by-assoc-and (under (ε) (CX01) B96.proved) Eq.refl Eq.refl

p5 : X0 • SWAP01 • CX01 ≈ X0 • CX01 • CX10
p5 = by-assoc-and (under (X0) (ε) B63.proved) Eq.refl Eq.refl

p6 : SWAP01 • X1 • CX01 ≈ X0 • CX01 • CX10
p6 = trans p4 (trans p5 (refl))

p7 : CX01 • CX10 • X1 ≈ X0 • CX01 • CX10
p7 = trans (sym p3) (trans p2 p6)

proved : CX01 • CX10 • X1 ≈ X0 • CX01 • CX10
proved = p7
