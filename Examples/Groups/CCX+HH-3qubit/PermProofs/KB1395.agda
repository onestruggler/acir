{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1395 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0014 as B14
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0091 as B91
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1394 as B1394

p0 : CCX02 • X2 • CX10 • CCX02 • CCX12 • CCX12 ≈ CCX12 • X2 • SWAP01 • CCX12
p0 = by-assoc-and (under (ε) (CCX12) B1394.proved) Eq.refl Eq.refl

p1 : CCX02 • X2 • CX10 • CCX02 • CCX12 • CCX12 ≈ CCX02 • X2 • CX10 • CCX02
p1 = by-assoc-and (under (CCX02 • X2 • CX10 • CCX02) (ε) B14.proved) Eq.refl Eq.refl

p2 : CCX12 • X2 • SWAP01 • CCX12 ≈ CCX02 • X2 • CX10 • CCX02
p2 = trans (sym p0) p1

p3 : CCX12 • X2 • SWAP01 • CCX12 ≈ CCX12 • X2 • CCX02 • SWAP01
p3 = by-assoc-and (under (CCX12 • X2) (ε) B91.proved) Eq.refl Eq.refl

p4 : CCX12 • X2 • SWAP01 • CCX12 ≈ CCX12 • X2 • CCX02 • SWAP01
p4 = trans p3 (refl)

p5 : CCX02 • X2 • CX10 • CCX02 ≈ CCX02 • X2 • CX10 • CCX02
p5 = refl

p6 : CCX12 • X2 • CCX02 • SWAP01 ≈ CCX02 • X2 • CX10 • CCX02
p6 = trans (sym p4) (trans p2 p5)

proved : CCX12 • X2 • CCX02 • SWAP01 ≈ CCX02 • X2 • CX10 • CCX02
proved = p6
