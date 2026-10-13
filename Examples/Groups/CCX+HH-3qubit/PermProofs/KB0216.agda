{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0216 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

import Examples.Groups.CCX+HH-3qubit.Tietze.cadd7 as Tcadd7
p0 : CX01 • CCX12 • CX01 ≈ CCX02 • CCX12 • CCX02
p0 = Tcadd7.proved

p1 : CX01 • CCX12 • CX01 ≈ CX01 • CCX12 • CX01
p1 = refl

p2 : CCX02 • CCX12 • CCX02 ≈ CCX02 • CCX12 • CCX02
p2 = refl

p3 : CX01 • CCX12 • CX01 ≈ CCX02 • CCX12 • CCX02
p3 = trans (sym p1) (trans p0 p2)

p4 : CCX02 • CCX12 • CCX02 ≈ CX01 • CCX12 • CX01
p4 = sym p3

proved : CCX02 • CCX12 • CCX02 ≈ CX01 • CCX12 • CX01
proved = p4
