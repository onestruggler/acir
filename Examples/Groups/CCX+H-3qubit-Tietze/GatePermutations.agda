{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.GatePermutations where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine

open import Examples.Groups.CCX+HH-3qubit.PermProofs.B000 using (module decodeCCX01 ; module decodeCCX02)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B002 using (module decodeCCX12 ; module decodeCX01 ; module decodeCX02)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B005 using (module decodeCX10)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B006 using (module decodeCX12)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B010 using (module decodeCX20)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B011 using (module decodeCX21)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B012 using (module decodeSWAP01)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B014 using (module decodeSWAP02)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B015 using (module decodeSWAP12)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B018 using (module decodeX0)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B019 using (module decodeX1 ; module decodeX2)

gateCCX01 : CCX01 ≈ p (s6)
gateCCX01 = by-assoc-and decodeCCX01.proved Eq.refl Eq.refl

gateCCX02 : CCX02 ≈ p (s6 • s5 • s6)
gateCCX02 = by-assoc-and decodeCCX02.proved Eq.refl Eq.refl

gateCCX12 : CCX12 ≈ p (s6 • s5 • s4 • s3 • s4 • s5 • s6)
gateCCX12 = by-assoc-and decodeCCX12.proved Eq.refl Eq.refl

gateCX01 : CX01 ≈ p (s5 • s4 • s6 • s5)
gateCX01 = by-assoc-and decodeCX01.proved Eq.refl Eq.refl

gateCX02 : CX02 ≈ p (s4 • s6)
gateCX02 = by-assoc-and decodeCX02.proved Eq.refl Eq.refl

gateCX10 : CX10 ≈ p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
gateCX10 = by-assoc-and decodeCX10.proved Eq.refl Eq.refl

gateCX12 : CX12 ≈ p (s2 • s6)
gateCX12 = by-assoc-and decodeCX12.proved Eq.refl Eq.refl

gateCX20 : CX20 ≈ p (s4 • s3 • s2 • s1 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6)
gateCX20 = by-assoc-and decodeCX20.proved Eq.refl Eq.refl

gateCX21 : CX21 ≈ p (s2 • s1 • s2 • s6 • s5 • s6)
gateCX21 = by-assoc-and decodeCX21.proved Eq.refl Eq.refl

gateSWAP01 : SWAP01 ≈ p (s3 • s2 • s4 • s3)
gateSWAP01 = by-assoc-and decodeSWAP01.proved Eq.refl Eq.refl

gateSWAP02 : SWAP02 ≈ p (s3 • s2 • s1 • s2 • s5 • s4 • s3 • s5)
gateSWAP02 = by-assoc-and decodeSWAP02.proved Eq.refl Eq.refl

gateSWAP12 : SWAP12 ≈ p (s1 • s5)
gateSWAP12 = by-assoc-and decodeSWAP12.proved Eq.refl Eq.refl

gateX0 : X0 ≈ p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
gateX0 = by-assoc-and decodeX0.proved Eq.refl Eq.refl

gateX1 : X1 ≈ p (s1 • s0 • s2 • s1 • s5 • s4 • s6 • s5)
gateX1 = by-assoc-and decodeX1.proved Eq.refl Eq.refl

gateX2 : X2 ≈ p (s0 • s2 • s4 • s6)
gateX2 = by-assoc-and decodeX2.proved Eq.refl Eq.refl

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

