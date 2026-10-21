{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PrimitiveFrames where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine

import Examples.Groups.CCX+HH-3qubit.GatePermutations as GP
open import Examples.Groups.CCX+HH-3qubit.FrameAliases.B000 using (module Ak4567)

open import Data.Fin.Base using (zero ; suc)

permX0 : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)
permX0 = checked (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)
  (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

backX0 : X04 • X15 • X26 • X37 ≈ X0
backX0 = sym (trans GP.gateX0 (by-assoc-and permX0 Eq.refl Eq.refl))

permCX01 : p (s5 • s4 • s6 • s5) ≈ p (s4 • s5 • s4 • s5 • s6 • s5)
permCX01 = checked (s5 • s4 • s6 • s5) (s4 • s5 • s4 • s5 • s6 • s5)
  (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

backCX01 : X46 • X57 ≈ CX01
backCX01 = sym (trans GP.gateCX01 (by-assoc-and permCX01 Eq.refl Eq.refl))

permCCX12 : p (s6 • s5 • s4 • s3 • s4 • s5 • s6) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3)
permCCX12 = checked (s6 • s5 • s4 • s3 • s4 • s5 • s6) (s3 • s4 • s5 • s6 • s5 • s4 • s3)
  (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

backCCX12 : X37 ≈ CCX12
backCCX12 = sym (trans GP.gateCCX12 (by-assoc-and permCCX12 Eq.refl Eq.refl))

neg-neg : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s1 • s0 • s2 • s1 • s5 • s4 • s6 • s5 • s0 • s2 • s4 • s6 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s1 • s0 • s2 • s1 • s5 • s4 • s6 • s5 • s0 • s2 • s4 • s6) ≈ p (ε)
neg-neg = checked (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s1 • s0 • s2 • s1 • s5 • s4 • s6 • s5 • s0 • s2 • s4 • s6 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s1 • s0 • s2 • s1 • s5 • s4 • s6 • s5 • s0 • s2 • s4 • s6) (ε)
  (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

rev-rev : p (s0 • s2 • s4 • s6 • s1 • s0 • s2 • s1 • s5 • s4 • s6 • s5 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s0 • s2 • s4 • s6 • s1 • s0 • s2 • s1 • s5 • s4 • s6 • s5 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) ≈ p (ε)
rev-rev = checked (s0 • s2 • s4 • s6 • s1 • s0 • s2 • s1 • s5 • s4 • s6 • s5 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s0 • s2 • s4 • s6 • s1 • s0 • s2 • s1 • s5 • s4 • s6 • s5 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) (ε)
  (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

neg-convert : (X0 • X1 • X2) • (X0 • X1 • X2) ≈ p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s1 • s0 • s2 • s1 • s5 • s4 • s6 • s5 • s0 • s2 • s4 • s6 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s1 • s0 • s2 • s1 • s5 • s4 • s6 • s5 • s0 • s2 • s4 • s6)
neg-convert = by-assoc-and (cong (cong GP.gateX0 (cong GP.gateX1 GP.gateX2)) (cong GP.gateX0 (cong GP.gateX1 GP.gateX2))) Eq.refl Eq.refl
neg-invol : (X0 • X1 • X2) • (X0 • X1 • X2) ≈ ε
neg-invol = trans neg-convert neg-neg

rev-convert : (X2 • X1 • X0) • (X2 • X1 • X0) ≈ p (s0 • s2 • s4 • s6 • s1 • s0 • s2 • s1 • s5 • s4 • s6 • s5 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s0 • s2 • s4 • s6 • s1 • s0 • s2 • s1 • s5 • s4 • s6 • s5 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
rev-convert = by-assoc-and (cong (cong GP.gateX2 (cong GP.gateX1 GP.gateX0)) (cong GP.gateX2 (cong GP.gateX1 GP.gateX0))) Eq.refl Eq.refl
rev-invol : (X2 • X1 • X0) • (X2 • X1 • X0) ≈ ε
rev-invol = trans rev-convert rev-rev

ccz-neg : X0 • X1 • X2 • m0 • X2 • X1 • X0 ≈ CCZ
ccz-neg = by-assoc-and (cong neg-invol (cong (refl {w = CCZ}) rev-invol)) Eq.refl Eq.refl

frame-left : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s1 • s0 • s2 • s1 • s5 • s4 • s6 • s5 • s0 • s2 • s4 • s6) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s5)
frame-left = checked (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s1 • s0 • s2 • s1 • s5 • s4 • s6 • s5 • s0 • s2 • s4 • s6) (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s5)
  (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

frame-right : p (s5 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s5) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s1 • s0 • s2 • s1 • s5 • s4 • s6 • s5 • s0 • s2 • s4 • s6)
frame-right = checked (s5 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s5) (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s1 • s0 • s2 • s1 • s5 • s4 • s6 • s5 • s0 • s2 • s4 • s6)
  (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

neg-rev : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s1 • s0 • s2 • s1 • s5 • s4 • s6 • s5 • s0 • s2 • s4 • s6 • s0 • s2 • s4 • s6 • s1 • s0 • s2 • s1 • s5 • s4 • s6 • s5 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) ≈ p (ε)
neg-rev = checked (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s1 • s0 • s2 • s1 • s5 • s4 • s6 • s5 • s0 • s2 • s4 • s6 • s0 • s2 • s4 • s6 • s1 • s0 • s2 • s1 • s5 • s4 • s6 • s5 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) (ε)
  (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

comm-frame : p (s5 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s5) • m0 ≈ m0 • p (s5 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s5)
comm-frame = commute-product (axiom r089) (commute-product (axiom r088) (commute-product (axiom r087) (commute-product (axiom r086) (commute-product (axiom r085) (commute-product (axiom r089) (commute-product (axiom r088) (commute-product (axiom r087) (commute-product (axiom r086) (commute-product (axiom r089) (commute-product (axiom r088) (commute-product (axiom r087) (commute-product (axiom r089) (commute-product (axiom r088) (axiom r089))))))))))))))

frame-step0 : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s1 • s0 • s2 • s1 • s5 • s4 • s6 • s5 • s0 • s2 • s4 • s6) • M0 ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • p (s5 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s5) • m0
frame-step0 = by-assoc-and (under ε m0 frame-left) Eq.refl Eq.refl

frame-step1 : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • p (s5 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s5) • m0 ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s5 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s5)
frame-step1 = cong refl comm-frame

frame-step2 : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s5 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s5) ≈ M7 • p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s1 • s0 • s2 • s1 • s5 • s4 • s6 • s5 • s0 • s2 • s4 • s6)
frame-step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • m0) ε frame-right) Eq.refl Eq.refl

move-neg : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s1 • s0 • s2 • s1 • s5 • s4 • s6 • s5 • s0 • s2 • s4 • s6) • M0 ≈ M7 • p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s1 • s0 • s2 • s1 • s5 • s4 • s6 • s5 • s0 • s2 • s4 • s6)
move-neg = trans frame-step0 (trans frame-step1 frame-step2)

frame-neg : X0 • X1 • X2 • m0 • X2 • X1 • X0 ≈ M7
frame-neg = trans converted (forget-frame (by-assoc-and move-neg Eq.refl Eq.refl)
  (by-assoc-and neg-rev Eq.refl Eq.refl))
  where
  converted : X0 • X1 • X2 • m0 • X2 • X1 • X0 ≈ p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s1 • s0 • s2 • s1 • s5 • s4 • s6 • s5 • s0 • s2 • s4 • s6) • M0 • p (s0 • s2 • s4 • s6 • s1 • s0 • s2 • s1 • s5 • s4 • s6 • s5 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  converted = by-assoc-and
    (cong (cong GP.gateX0 (cong GP.gateX1 GP.gateX2))
      (cong (refl {w = m0}) (cong GP.gateX2 (cong GP.gateX1 GP.gateX0)))) Eq.refl Eq.refl

backCCZ : M7 ≈ CCZ
backCCZ = trans (sym frame-neg) ccz-neg

backNK : K0123 ≈ NK
backNK = by-assoc Eq.refl

backK4567 : K4567 ≈ X0 • NK • X0
backK4567 = sym Ak4567.proved
