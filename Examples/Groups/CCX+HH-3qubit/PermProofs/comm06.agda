{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.comm06 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0003 as B3
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 as B45
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0150 as B150
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0152 as B152
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0161 as B161
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0815 as B815
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0890 as B890

p0 : X0 • X1 • CCX01 • X1 • X0 • CCX01 ≈ X0 • CX02 • CCX01 • X0 • CCX01
p0 = by-assoc-and (under (X0) (X0 • CCX01) B150.proved) Eq.refl Eq.refl

p1 : X0 • CX02 • CCX01 • X0 • CCX01 ≈ X0 • CX02 • X0 • CX12
p1 = by-assoc-and (under (X0 • CX02) (ε) B152.proved) Eq.refl Eq.refl

p2 : X0 • CX02 • X0 • CX12 ≈ X2 • CX02 • CX12
p2 = by-assoc-and (under (ε) (CX12) B161.proved) Eq.refl Eq.refl

p3 : X0 • X1 • CCX01 • X1 • X0 • CCX01 ≈ X2 • CX02 • CX12
p3 = trans p0 (trans p1 (trans p2 (refl)))

p4 : CCX01 • X0 • X1 • CCX01 • X1 • X0 ≈ X1 • CX02 • X0 • CX12 • X1 • X0
p4 = by-assoc-and (under (ε) (X1 • X0) B815.proved) Eq.refl Eq.refl

p5 : X1 • CX02 • X0 • CX12 • X1 • X0 ≈ X0 • CX02 • CX12 • X1 • X1 • X0
p5 = by-assoc-and (under (ε) (X1 • X0) B890.proved) Eq.refl Eq.refl

p6 : X0 • CX02 • CX12 • X1 • X1 • X0 ≈ X0 • CX02 • CX12 • X0
p6 = by-assoc-and (under (X0 • CX02 • CX12) (X0) B3.proved) Eq.refl Eq.refl

p7 : X0 • CX02 • CX12 • X0 ≈ X0 • CX02 • X0 • CX12
p7 = by-assoc-and (under (X0 • CX02) (ε) B45.proved) Eq.refl Eq.refl

p8 : X0 • CX02 • X0 • CX12 ≈ X2 • CX02 • CX12
p8 = by-assoc-and (under (ε) (CX12) B161.proved) Eq.refl Eq.refl

p9 : CCX01 • X0 • X1 • CCX01 • X1 • X0 ≈ X2 • CX02 • CX12
p9 = trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (refl)))))

proved : X0 • X1 • CCX01 • X1 • X0 • CCX01 ≈ CCX01 • X0 • X1 • CCX01 • X1 • X0
proved = trans p3 (sym p9)
