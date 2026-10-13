{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0005 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX10 as Telim_CX10
p0 : CX10 • CX10 ≈ ε
p0 = Telim_CX10.proved

p1 : CX10 • CX10 ≈ CX10 • CX10
p1 = refl

p2 : ε ≈ ε
p2 = refl

p3 : CX10 • CX10 ≈ ε
p3 = trans (sym p1) (trans p0 p2)

proved : CX10 • CX10 ≈ ε
proved = p3
