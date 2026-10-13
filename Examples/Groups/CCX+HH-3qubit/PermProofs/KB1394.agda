{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1394 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0010 as B10
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1309 as B1309

p0 : CCX02 • CCX02 • CCX12 • X2 • SWAP01 ≈ CCX02 • X2 • CX10 • CCX02 • CCX12
p0 = by-assoc-and (under (CCX02) (ε) B1309.proved) Eq.refl Eq.refl

p1 : CCX02 • CCX02 • CCX12 • X2 • SWAP01 ≈ CCX12 • X2 • SWAP01
p1 = by-assoc-and (under (ε) (CCX12 • X2 • SWAP01) B10.proved) Eq.refl Eq.refl

p2 : CCX02 • X2 • CX10 • CCX02 • CCX12 ≈ CCX12 • X2 • SWAP01
p2 = trans (sym p0) p1

p3 : CCX02 • X2 • CX10 • CCX02 • CCX12 ≈ CCX02 • X2 • CX10 • CCX02 • CCX12
p3 = refl

p4 : CCX12 • X2 • SWAP01 ≈ CCX12 • X2 • SWAP01
p4 = refl

p5 : CCX02 • X2 • CX10 • CCX02 • CCX12 ≈ CCX12 • X2 • SWAP01
p5 = trans (sym p3) (trans p2 p4)

proved : CCX02 • X2 • CX10 • CCX02 • CCX12 ≈ CCX12 • X2 • SWAP01
proved = p5
