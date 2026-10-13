{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0089 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

p0 : CCX02 ≈ SWAP01 • CCX12 • SWAP01
p0 = by-assoc-and (axiom r014) Eq.refl Eq.refl

p1 : CCX02 ≈ CCX02
p1 = refl

p2 : SWAP01 • CCX12 • SWAP01 ≈ SWAP01 • CCX12 • SWAP01
p2 = refl

p3 : CCX02 ≈ SWAP01 • CCX12 • SWAP01
p3 = trans (sym p1) (trans p0 p2)

p4 : SWAP01 • CCX12 • SWAP01 ≈ CCX02
p4 = sym p3

proved : SWAP01 • CCX12 • SWAP01 ≈ CCX02
proved = p4
