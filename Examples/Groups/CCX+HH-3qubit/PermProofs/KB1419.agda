{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1419 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0014 as B14
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1379 as B1379

p0 : CCX12 • CCX12 • CCX02 • X2 • SWAP01 ≈ CCX12 • X2 • CX01 • CCX12 • CCX02
p0 = by-assoc-and (under (CCX12) (ε) B1379.proved) Eq.refl Eq.refl

p1 : CCX12 • CCX12 • CCX02 • X2 • SWAP01 ≈ CCX02 • X2 • SWAP01
p1 = by-assoc-and (under (ε) (CCX02 • X2 • SWAP01) B14.proved) Eq.refl Eq.refl

p2 : CCX12 • X2 • CX01 • CCX12 • CCX02 ≈ CCX02 • X2 • SWAP01
p2 = trans (sym p0) p1

p3 : CCX12 • X2 • CX01 • CCX12 • CCX02 ≈ CCX12 • X2 • CX01 • CCX12 • CCX02
p3 = refl

p4 : CCX02 • X2 • SWAP01 ≈ CCX02 • X2 • SWAP01
p4 = refl

p5 : CCX12 • X2 • CX01 • CCX12 • CCX02 ≈ CCX02 • X2 • SWAP01
p5 = trans (sym p3) (trans p2 p4)

proved : CCX12 • X2 • CX01 • CCX12 • CCX02 ≈ CCX02 • X2 • SWAP01
proved = p5
