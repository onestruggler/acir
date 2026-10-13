{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CCX2 as Telim_CCX2
p0 : CCX01 • CCX01 ≈ ε
p0 = Telim_CCX2.proved

p1 : CCX01 • CCX01 ≈ CCX01 • CCX01
p1 = refl

p2 : ε ≈ ε
p2 = refl

p3 : CCX01 • CCX01 ≈ ε
p3 = trans (sym p1) (trans p0 p2)

proved : CCX01 • CCX01 ≈ ε
proved = p3
