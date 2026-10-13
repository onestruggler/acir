{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.GatePermutations where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine

import Examples.Groups.CCX+HH-3qubit.PermProofs.decodeCCX01 as DCCX01
import Examples.Groups.CCX+HH-3qubit.PermProofs.decodeCCX02 as DCCX02
import Examples.Groups.CCX+HH-3qubit.PermProofs.decodeCCX12 as DCCX12
import Examples.Groups.CCX+HH-3qubit.PermProofs.decodeCX01 as DCX01
import Examples.Groups.CCX+HH-3qubit.PermProofs.decodeCX02 as DCX02
import Examples.Groups.CCX+HH-3qubit.PermProofs.decodeCX10 as DCX10
import Examples.Groups.CCX+HH-3qubit.PermProofs.decodeCX12 as DCX12
import Examples.Groups.CCX+HH-3qubit.PermProofs.decodeCX20 as DCX20
import Examples.Groups.CCX+HH-3qubit.PermProofs.decodeCX21 as DCX21
import Examples.Groups.CCX+HH-3qubit.PermProofs.decodeSWAP01 as DSWAP01
import Examples.Groups.CCX+HH-3qubit.PermProofs.decodeSWAP02 as DSWAP02
import Examples.Groups.CCX+HH-3qubit.PermProofs.decodeSWAP12 as DSWAP12
import Examples.Groups.CCX+HH-3qubit.PermProofs.decodeX0 as DX0
import Examples.Groups.CCX+HH-3qubit.PermProofs.decodeX1 as DX1
import Examples.Groups.CCX+HH-3qubit.PermProofs.decodeX2 as DX2

gateCCX01 : CCX01 ≈ p (s6)
gateCCX01 = by-assoc-and DCCX01.proved Eq.refl Eq.refl

gateCCX02 : CCX02 ≈ p (s6 • s5 • s6)
gateCCX02 = by-assoc-and DCCX02.proved Eq.refl Eq.refl

gateCCX12 : CCX12 ≈ p (s6 • s5 • s4 • s3 • s4 • s5 • s6)
gateCCX12 = by-assoc-and DCCX12.proved Eq.refl Eq.refl

gateCX01 : CX01 ≈ p (s5 • s4 • s6 • s5)
gateCX01 = by-assoc-and DCX01.proved Eq.refl Eq.refl

gateCX02 : CX02 ≈ p (s4 • s6)
gateCX02 = by-assoc-and DCX02.proved Eq.refl Eq.refl

gateCX10 : CX10 ≈ p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
gateCX10 = by-assoc-and DCX10.proved Eq.refl Eq.refl

gateCX12 : CX12 ≈ p (s2 • s6)
gateCX12 = by-assoc-and DCX12.proved Eq.refl Eq.refl

gateCX20 : CX20 ≈ p (s4 • s3 • s2 • s1 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6)
gateCX20 = by-assoc-and DCX20.proved Eq.refl Eq.refl

gateCX21 : CX21 ≈ p (s2 • s1 • s2 • s6 • s5 • s6)
gateCX21 = by-assoc-and DCX21.proved Eq.refl Eq.refl

gateSWAP01 : SWAP01 ≈ p (s3 • s2 • s4 • s3)
gateSWAP01 = by-assoc-and DSWAP01.proved Eq.refl Eq.refl

gateSWAP02 : SWAP02 ≈ p (s3 • s2 • s1 • s2 • s5 • s4 • s3 • s5)
gateSWAP02 = by-assoc-and DSWAP02.proved Eq.refl Eq.refl

gateSWAP12 : SWAP12 ≈ p (s1 • s5)
gateSWAP12 = by-assoc-and DSWAP12.proved Eq.refl Eq.refl

gateX0 : X0 ≈ p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
gateX0 = by-assoc-and DX0.proved Eq.refl Eq.refl

gateX1 : X1 ≈ p (s1 • s0 • s2 • s1 • s5 • s4 • s6 • s5)
gateX1 = by-assoc-and DX1.proved Eq.refl Eq.refl

gateX2 : X2 ≈ p (s0 • s2 • s4 • s6)
gateX2 = by-assoc-and DX2.proved Eq.refl Eq.refl

gatet01 : t01 ≈ p (s0)
gatet01 = by-assoc Eq.refl

gatet12 : t12 ≈ p (s1)
gatet12 = by-assoc Eq.refl

gatet23 : t23 ≈ p (s2)
gatet23 = by-assoc Eq.refl

gatet34 : t34 ≈ p (s3)
gatet34 = by-assoc Eq.refl

gatet45 : t45 ≈ p (s4)
gatet45 = by-assoc Eq.refl

gatet56 : t56 ≈ p (s5)
gatet56 = by-assoc Eq.refl

gatet67 : t67 ≈ p (s6)
gatet67 = by-assoc Eq.refl

