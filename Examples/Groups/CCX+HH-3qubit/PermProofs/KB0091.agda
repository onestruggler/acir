{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0091 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0000 as B0
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0089 as B89

p0 : SWAP01 • CCX12 • SWAP01 • SWAP01 ≈ CCX02 • SWAP01
p0 = by-assoc-and (under (ε) (SWAP01) B89.proved) Eq.refl Eq.refl

p1 : SWAP01 • CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • CCX12
p1 = by-assoc-and (under (SWAP01 • CCX12) (ε) B0.proved) Eq.refl Eq.refl

p2 : CCX02 • SWAP01 ≈ SWAP01 • CCX12
p2 = trans (sym p0) p1

p3 : CCX02 • SWAP01 ≈ CCX02 • SWAP01
p3 = refl

p4 : SWAP01 • CCX12 ≈ SWAP01 • CCX12
p4 = refl

p5 : CCX02 • SWAP01 ≈ SWAP01 • CCX12
p5 = trans (sym p3) (trans p2 p4)

p6 : SWAP01 • CCX12 ≈ CCX02 • SWAP01
p6 = sym p5

proved : SWAP01 • CCX12 ≈ CCX02 • SWAP01
proved = p6
