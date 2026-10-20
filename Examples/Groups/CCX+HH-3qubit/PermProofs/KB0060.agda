{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0060 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX12 ; CX21 ; SWAP12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0041 as B41

import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_d as Tsymmetry_CX_d
p0 : CX12 ≈ SWAP12 • CX21 • SWAP12
p0 = Tsymmetry_CX_d.proved

p1 : CX12 ≈ CX12
p1 = refl

p2 : SWAP12 • CX21 • SWAP12 ≈ SWAP12 • CX12 • CX21
p2 = by-assoc-and (under (SWAP12) (ε) B41.proved) Eq.refl Eq.refl

p3 : SWAP12 • CX21 • SWAP12 ≈ SWAP12 • CX12 • CX21
p3 = trans p2 (refl)

p4 : CX12 ≈ SWAP12 • CX12 • CX21
p4 = trans (sym p1) (trans p0 p3)

p5 : SWAP12 • CX12 • CX21 ≈ CX12
p5 = sym p4

proved : SWAP12 • CX12 • CX21 ≈ CX12
proved = p5
