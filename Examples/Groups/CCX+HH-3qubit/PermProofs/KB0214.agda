{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0214 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

import Examples.Groups.CCX+HH-3qubit.Tietze.cadd5 as Tcadd5
p0 : CX12 • CCX02 • CX12 ≈ CCX01 • CCX02 • CCX01
p0 = Tcadd5.proved

p1 : CX12 • CCX02 • CX12 ≈ CX12 • CCX02 • CX12
p1 = refl

p2 : CCX01 • CCX02 • CCX01 ≈ CCX01 • CCX02 • CCX01
p2 = refl

p3 : CX12 • CCX02 • CX12 ≈ CCX01 • CCX02 • CCX01
p3 = trans (sym p1) (trans p0 p2)

p4 : CCX01 • CCX02 • CCX01 ≈ CX12 • CCX02 • CX12
p4 = sym p3

proved : CCX01 • CCX02 • CCX01 ≈ CX12 • CCX02 • CX12
proved = p4
