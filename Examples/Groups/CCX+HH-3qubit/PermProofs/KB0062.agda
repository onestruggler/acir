{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0062 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0042 as B42

import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_e as Tsymmetry_CX_e
p0 : CX01 ≈ SWAP01 • CX10 • SWAP01
p0 = Tsymmetry_CX_e.proved

p1 : CX01 ≈ CX01
p1 = refl

p2 : SWAP01 • CX10 • SWAP01 ≈ SWAP01 • CX01 • CX10
p2 = by-assoc-and (under (SWAP01) (ε) B42.proved) Eq.refl Eq.refl

p3 : SWAP01 • CX10 • SWAP01 ≈ SWAP01 • CX01 • CX10
p3 = trans p2 (refl)

p4 : CX01 ≈ SWAP01 • CX01 • CX10
p4 = trans (sym p1) (trans p0 p3)

p5 : SWAP01 • CX01 • CX10 ≈ CX01
p5 = sym p4

proved : SWAP01 • CX01 • CX10 ≈ CX01
proved = p5
