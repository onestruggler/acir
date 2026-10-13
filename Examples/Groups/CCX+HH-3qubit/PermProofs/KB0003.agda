{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0003 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

import Examples.Groups.CCX+HH-3qubit.Tietze.elim_X1 as Telim_X1
p0 : X1 • X1 ≈ ε
p0 = Telim_X1.proved

p1 : X1 • X1 ≈ X1 • X1
p1 = refl

p2 : ε ≈ ε
p2 = refl

p3 : X1 • X1 ≈ ε
p3 = trans (sym p1) (trans p0 p2)

proved : X1 • X1 ≈ ε
proved = p3
