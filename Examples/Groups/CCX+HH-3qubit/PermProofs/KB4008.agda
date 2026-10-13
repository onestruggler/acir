{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB4008 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0196 as B196
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0224 as B224
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0662 as B662
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB3634 as B3634

p0 : CCX02 • X0 • CCX01 • CX21 • X2 • CX21 ≈ X0 • CCX01 • CCX02 • X2 • CX21
p0 = by-assoc-and (under (ε) (X2 • CX21) B662.proved) Eq.refl Eq.refl

p1 : CCX02 • X0 • CCX01 • CX21 • X2 • CX21 ≈ CCX02 • X0 • CCX01 • X1 • X2
p1 = by-assoc-and (under (CCX02 • X0 • CCX01) (ε) B196.proved) Eq.refl Eq.refl

p2 : X0 • CCX01 • CCX02 • X2 • CX21 ≈ CCX02 • X0 • CCX01 • X1 • X2
p2 = trans (sym p0) p1

p3 : X0 • CCX01 • CCX02 • X2 • CX21 ≈ X0 • CCX01 • CCX02 • X2 • CX21
p3 = refl

p4 : CCX02 • X0 • CCX01 • X1 • X2 ≈ CCX02 • X0 • X2 • CCX01 • X1
p4 = by-assoc-and (under (CCX02 • X0) (ε) B224.proved) Eq.refl Eq.refl

p5 : CCX02 • X0 • X2 • CCX01 • X1 ≈ X1 • CCX02 • CX02 • X0 • CCX01
p5 = by-assoc-and (under (ε) (ε) B3634.proved) Eq.refl Eq.refl

p6 : CCX02 • X0 • CCX01 • X1 • X2 ≈ X1 • CCX02 • CX02 • X0 • CCX01
p6 = trans p4 (trans p5 (refl))

p7 : X0 • CCX01 • CCX02 • X2 • CX21 ≈ X1 • CCX02 • CX02 • X0 • CCX01
p7 = trans (sym p3) (trans p2 p6)

p8 : X1 • CCX02 • CX02 • X0 • CCX01 ≈ X0 • CCX01 • CCX02 • X2 • CX21
p8 = sym p7

proved : X1 • CCX02 • CX02 • X0 • CCX01 ≈ X0 • CCX01 • CCX02 • X2 • CX21
proved = p8
