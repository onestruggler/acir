{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0219 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0215 as B215
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0216 as B216

import Examples.Groups.CCX+HH-3qubit.Tietze.cflip2 as Tcflip2
p0 : CCX02 • CCX12 • CCX02 ≈ CCX12 • CCX02 • CCX12
p0 = Tcflip2.proved

p1 : CCX02 • CCX12 • CCX02 ≈ CX01 • CCX12 • CX01
p1 = by-assoc-and (under (ε) (ε) B216.proved) Eq.refl Eq.refl

p2 : CCX02 • CCX12 • CCX02 ≈ CX01 • CCX12 • CX01
p2 = trans p1 (refl)

p3 : CCX12 • CCX02 • CCX12 ≈ CX10 • CCX02 • CX10
p3 = by-assoc-and (under (ε) (ε) B215.proved) Eq.refl Eq.refl

p4 : CCX12 • CCX02 • CCX12 ≈ CX10 • CCX02 • CX10
p4 = trans p3 (refl)

p5 : CX01 • CCX12 • CX01 ≈ CX10 • CCX02 • CX10
p5 = trans (sym p2) (trans p0 p4)

p6 : CX10 • CCX02 • CX10 ≈ CX01 • CCX12 • CX01
p6 = sym p5

proved : CX10 • CCX02 • CX10 ≈ CX01 • CCX12 • CX01
proved = p6
