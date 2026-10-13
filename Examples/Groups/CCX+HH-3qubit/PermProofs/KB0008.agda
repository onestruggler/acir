{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0008 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX02 as Telim_CX02
p0 : CX02 • CX02 ≈ ε
p0 = Telim_CX02.proved

p1 : CX02 • CX02 ≈ CX02 • CX02
p1 = refl

p2 : ε ≈ ε
p2 = refl

p3 : CX02 • CX02 ≈ ε
p3 = trans (sym p1) (trans p0 p2)

proved : CX02 • CX02 ≈ ε
proved = p3
