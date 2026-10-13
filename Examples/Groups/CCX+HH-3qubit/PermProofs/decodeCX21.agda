{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.decodeCX21 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0010 as B10
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0012 as B12
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0140 as B140
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0153 as B153
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0166 as B166

p0 : CX21 ≈ CX21
p0 = refl

p1 : X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01 ≈ CX12 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01
p1 = by-assoc-and (under (ε) (X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01) B153.proved) Eq.refl Eq.refl

p2 : CX12 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01 ≈ X0 • CCX01 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01
p2 = by-assoc-and (under (ε) (CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01) B140.proved) Eq.refl Eq.refl

p3 : X0 • CCX01 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01 ≈ X0 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01
p3 = by-assoc-and (under (X0) (CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01) B11.proved) Eq.refl Eq.refl

p4 : X0 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01 ≈ X0 • CCX02 • CCX01 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01
p4 = by-assoc-and (under (X0 • CCX02 • CCX01) (CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01) B12.proved) Eq.refl Eq.refl

p5 : X0 • CCX02 • CCX01 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01 ≈ X0 • CCX02 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01
p5 = by-assoc-and (under (X0 • CCX02) (X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01) B11.proved) Eq.refl Eq.refl

p6 : X0 • CCX02 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01 ≈ CX21 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01
p6 = by-assoc-and (under (ε) (CCX01 • CCX01 • CCX02 • CCX01 • CCX01) B166.proved) Eq.refl Eq.refl

p7 : CX21 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01 ≈ CX21 • CCX02 • CCX02 • CCX01 • CCX01
p7 = by-assoc-and (under (CX21 • CCX02) (CCX02 • CCX01 • CCX01) B11.proved) Eq.refl Eq.refl

p8 : CX21 • CCX02 • CCX02 • CCX01 • CCX01 ≈ CX21 • CCX01 • CCX01
p8 = by-assoc-and (under (CX21) (CCX01 • CCX01) B10.proved) Eq.refl Eq.refl

p9 : CX21 • CCX01 • CCX01 ≈ CX21
p9 = by-assoc-and (under (CX21) (ε) B11.proved) Eq.refl Eq.refl

p10 : X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01 ≈ CX21
p10 = trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (refl)))))))))

proved : CX21 ≈ X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01
proved = trans p0 (sym p10)
