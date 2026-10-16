------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (placed)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Wins.WP03 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)

wp0325 : Complete 4 → ⟪ (CS12 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS12 ∷ []) ⟫ʷ
wp0325 c4 = pw3 c4 (CS12 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS12 ∷ []) tt tt Eq.refl

wp0326 : Complete 4 → ⟪ (CS12⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS12⁻ ∷ []) ⟫ʷ
wp0326 c4 = pw3 c4 (CS12⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wp0327 : Complete 4 → ⟪ (CS03 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS03 ∷ []) ⟫ʷ
wp0327 c4 = pw2 c4 (CS03 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS03 ∷ []) tt tt Eq.refl

wp0328 : Complete 4 → ⟪ (CS03⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0328 c4 = pw2 c4 (CS03⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0329 : Complete 4 → ⟪ (Toff014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ Toff014 ∷ []) ⟫ʷ
wp0329 c4 = pw2 c4 (Toff014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ Toff014 ∷ []) tt tt Eq.refl

wp0330 : Complete 4 → ⟪ (CCZ014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ CCZ014 ∷ []) ⟫ʷ
wp0330 c4 = pw2 c4 (CCZ014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0331 : Complete 4 → ⟪ (CS03 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS03 ∷ []) ⟫ʷ
wp0331 c4 = pw1 c4 (CS03 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS03 ∷ []) tt tt Eq.refl

wp0332 : Complete 4 → ⟪ (CS03⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0332 c4 = pw1 c4 (CS03⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0333 : Complete 4 → ⟪ (CCZ024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CCZ024 ∷ []) ⟫ʷ
wp0333 c4 = pw1 c4 (CCZ024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0334 : Complete 4 → ⟪ (Toff024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ Toff024 ∷ []) ⟫ʷ
wp0334 c4 = pw1 c4 (Toff024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ Toff024 ∷ []) tt tt Eq.refl

wp0335 : Complete 4 → ⟪ (CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0335 c4 = pw2 c4 (CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0336 : Complete 4 → ⟪ (CCZ034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ CCZ034 ∷ []) ⟫ʷ
wp0336 c4 = pw1 c4 (CCZ034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0337 : Complete 4 → ⟪ (S4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS03⁻ ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wp0337 c4 = pw1 c4 (S4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wp0338 : Complete 4 → ⟪ (S4 ∷ X4 ∷ CS03 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS03 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wp0338 c4 = pw1 c4 (S4 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wp0339 : Complete 4 → ⟪ (S4 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff204 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wp0339 c4 = pw1 c4 (S4 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wp0340 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS03⁻ ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0340 c4 = pw1 c4 (CS04 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0341 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff314 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0341 c4 = pw2 c4 (CS04 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (X4 ∷ Toff314 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0342 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ CS03 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS03 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0342 c4 = pw1 c4 (CS04 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0343 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS12 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0343 c4 = pw3 c4 (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0344 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CX13 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0344 c4 = pw2 c4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (X4 ∷ CX13 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0345 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS23⁻ ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0345 c4 = pw1 c4 (CS04 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (X4 ∷ CS23⁻ ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0346 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ CS23 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS23 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0346 c4 = pw1 c4 (CS04 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (X4 ∷ CS23 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0347 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff204 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0347 c4 = pw1 c4 (CS04 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0348 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS03⁻ ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wp0348 c4 = pw2 c4 (CS14 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wp0349 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS03 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wp0349 c4 = pw2 c4 (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wp0350 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff204 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wp0350 c4 = pw3 c4 (CS14 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wp0351 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS03⁻ ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wp0351 c4 = pw1 c4 (CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wp0352 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS03 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wp0352 c4 = pw1 c4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wp0353 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff204 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wp0353 c4 = pw1 c4 (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wp0354 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS03⁻ ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wp0354 c4 = pw1 c4 (CS34 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wp0355 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ CS03 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS03 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wp0355 c4 = pw1 c4 (CS34 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wp0356 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff204 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wp0356 c4 = pw1 c4 (CS34 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wp0357 : Complete 4 → ⟪ (S4⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS03⁻ ∷ X4 ∷ S4⁻ ∷ []) ⟫ʷ
wp0357 c4 = pw1 c4 (S4⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ X4 ∷ S4⁻ ∷ []) tt tt Eq.refl

wp0358 : Complete 4 → ⟪ (S4⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS03 ∷ X4 ∷ S4⁻ ∷ []) ⟫ʷ
wp0358 c4 = pw1 c4 (S4⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ S4⁻ ∷ []) tt tt Eq.refl

wp0359 : Complete 4 → ⟪ (S4⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff204 ∷ X4 ∷ S4⁻ ∷ []) ⟫ʷ
wp0359 c4 = pw1 c4 (S4⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ S4⁻ ∷ []) tt tt Eq.refl

wp0360 : Complete 4 → ⟪ (K0 ∷ CS04 ∷ K0 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ []) ⟫ʷ
wp0360 c4 = pw2 c4 (K0 ∷ CS04 ∷ K0 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ []) tt tt Eq.refl

wp0361 : Complete 4 → ⟪ (K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff314 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ []) ⟫ʷ
wp0361 c4 = pw2 c4 (K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (X4 ∷ Toff314 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ []) tt tt Eq.refl

wp0362 : Complete 4 → ⟪ (K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ []) ⟫ʷ
wp0362 c4 = pw1 c4 (K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ []) tt tt Eq.refl

wp0363 : Complete 4 → ⟪ (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS03⁻ ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ []) ⟫ʷ
wp0363 c4 = pw2 c4 (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ []) tt tt Eq.refl

wp0364 : Complete 4 → ⟪ (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS03 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ []) ⟫ʷ
wp0364 c4 = pw2 c4 (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ []) tt tt Eq.refl

wp0365 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wp0365 c4 = pw3 c4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wp0366 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wp0366 c4 = pw2 c4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wp0367 : Complete 4 → ⟪ (CS01 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CS01 ∷ []) ⟫ʷ
wp0367 c4 = pw2 c4 (CS01 ∷ Toff413 ∷ []) (Toff413 ∷ CS01 ∷ []) tt tt Eq.refl

wp0368 : Complete 4 → ⟪ (CS01 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CS01 ∷ []) ⟫ʷ
wp0368 c4 = pw2 c4 (CS01 ∷ CS04 ∷ []) (CS04 ∷ CS01 ∷ []) tt tt Eq.refl

wp0369 : Complete 4 → ⟪ (CS01 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ CS01 ∷ []) ⟫ʷ
wp0369 c4 = pw2 c4 (CS01 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CS01 ∷ []) tt tt Eq.refl

wp0370 : Complete 4 → ⟪ (CS02⁻ ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ CS02⁻ ∷ []) ⟫ʷ
wp0370 c4 = pw3 c4 (CS02⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS02⁻ ∷ []) tt tt Eq.refl

wp0371 : Complete 4 → ⟪ (CS02⁻ ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS02⁻ ∷ []) ⟫ʷ
wp0371 c4 = pw1 c4 (CS02⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS02⁻ ∷ []) tt tt Eq.refl

wp0372 : Complete 4 → ⟪ (CS02⁻ ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CS02⁻ ∷ []) ⟫ʷ
wp0372 c4 = pw3 c4 (CS02⁻ ∷ CS14 ∷ []) (CS14 ∷ CS02⁻ ∷ []) tt tt Eq.refl

wp0373 : Complete 4 → ⟪ (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ []) ⟫ʷ
wp0373 c4 = pw1 c4 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (Toff024 ∷ []) tt tt Eq.refl

wp0374 : Complete 4 → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) ⟫ʷ
wp0374 c4 = pw1 c4 (CCZ024 ∷ []) (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) tt tt Eq.refl

wp0375 : Complete 4 → ⟪ (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ []) ⟫ʷ
wp0375 c4 = pw2 c4 (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ []) tt tt Eq.refl

wp0376 : Complete 4 → ⟪ (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff314 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ []) ⟫ʷ
wp0376 c4 = pw2 c4 (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (X4 ∷ Toff314 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ []) tt tt Eq.refl

wp0377 : Complete 4 → ⟪ (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ []) ⟫ʷ
wp0377 c4 = pw1 c4 (K0 ∷ CS04 ∷ K0⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ K0⁻ ∷ []) tt tt Eq.refl

wp0378 : Complete 4 → ⟪ (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ []) ⟫ʷ
wp0378 c4 = pw3 c4 (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff214 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ []) tt tt Eq.refl

wp0379 : Complete 4 → ⟪ (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff214 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ []) ⟫ʷ
wp0379 c4 = pw3 c4 (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff214 ∷ X4 ∷ []) (X4 ∷ Toff214 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ []) tt tt Eq.refl

wp0380 : Complete 4 → ⟪ (CS04⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS13 ∷ X4 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0380 c4 = pw2 c4 (CS04⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ X4 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0381 : Complete 4 → ⟪ (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CX12 ∷ X4 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0381 c4 = pw3 c4 (CS04⁻ ∷ X4 ∷ CX12 ∷ X4 ∷ []) (X4 ∷ CX12 ∷ X4 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0382 : Complete 4 → ⟪ (CS04⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS23⁻ ∷ X4 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0382 c4 = pw1 c4 (CS04⁻ ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (X4 ∷ CS23⁻ ∷ X4 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0383 : Complete 4 → ⟪ (CS04⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS23 ∷ X4 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0383 c4 = pw1 c4 (CS04⁻ ∷ X4 ∷ CS23 ∷ X4 ∷ []) (X4 ∷ CS23 ∷ X4 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0384 : Complete 4 → ⟪ (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ []) ⟫ʷ
wp0384 c4 = pw1 c4 (K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X4 ∷ Toff304 ∷ X4 ∷ []) (X4 ∷ Toff304 ∷ X4 ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS04⁻ ∷ K0⁻ ∷ K0 ∷ CX24 ∷ K0⁻ ∷ K0 ∷ CS02 ∷ K0⁻ ∷ []) tt tt Eq.refl

wp0385 : Complete 4 → ⟪ (CCZ234 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS03⁻ ∷ X4 ∷ CCZ234 ∷ []) ⟫ʷ
wp0385 c4 = pw1 c4 (CCZ234 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ X4 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp0386 : Complete 4 → ⟪ (CCZ234 ∷ X4 ∷ CS03 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS03 ∷ X4 ∷ CCZ234 ∷ []) ⟫ʷ
wp0386 c4 = pw1 c4 (CCZ234 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp0387 : Complete 4 → ⟪ (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS03⁻ ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) ⟫ʷ
wp0387 c4 = pw2 c4 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) tt tt Eq.refl

wp0388 : Complete 4 → ⟪ (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS03 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) ⟫ʷ
wp0388 c4 = pw2 c4 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) tt tt Eq.refl

wp0389 : Complete 4 → ⟪ (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS03⁻ ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) ⟫ʷ
wp0389 c4 = pw2 c4 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) tt tt Eq.refl

wp0390 : Complete 4 → ⟪ (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS03 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) ⟫ʷ
wp0390 c4 = pw2 c4 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) tt tt Eq.refl

wp0391 : Complete 4 → ⟪ (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff203 ∷ X4 ∷ CX34 ∷ []) ⟫ʷ
wp0391 c4 = pw1 c4 (CX34 ∷ X4 ∷ Toff203 ∷ X4 ∷ []) (X4 ∷ Toff203 ∷ X4 ∷ CX34 ∷ []) tt tt Eq.refl

wp0392 : Complete 4 → ⟪ (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ []) ⟫ʷ
wp0392 c4 = pw3 c4 (CS14⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (X4 ∷ CS02 ∷ X4 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wp0393 : Complete 4 → ⟪ (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CX03 ∷ X4 ∷ CS14⁻ ∷ []) ⟫ʷ
wp0393 c4 = pw2 c4 (CS14⁻ ∷ X4 ∷ CX03 ∷ X4 ∷ []) (X4 ∷ CX03 ∷ X4 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wp0394 : Complete 4 → ⟪ (Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ []) ⟫ʷ
wp0394 c4 = pw1 c4 (Toff024 ∷ []) (Toff024 ∷ []) tt tt Eq.refl

wp0395 : Complete 4 → ⟪ (S4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ023 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wp0395 c4 = pw1 c4 (S4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (X4 ∷ CCZ023 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wp0396 : Complete 4 → ⟪ (S4 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff014 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wp0396 c4 = pw2 c4 (S4 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wp0397 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS13⁻ ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0397 c4 = pw2 c4 (CS04 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13⁻ ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0398 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff324 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0398 c4 = pw1 c4 (CS04 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (X4 ∷ Toff324 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0399 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ CS13 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS13 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0399 c4 = pw2 c4 (CS04 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0400 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ023 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0400 c4 = pw1 c4 (CS04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (X4 ∷ CCZ023 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0401 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff014 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0401 c4 = pw2 c4 (CS04 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0402 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wp0402 c4 = pw2 c4 (CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wp0403 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ023 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wp0403 c4 = pw1 c4 (CS24 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (X4 ∷ CCZ023 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wp0404 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff014 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wp0404 c4 = pw3 c4 (CS24 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wp0405 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ023 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wp0405 c4 = pw1 c4 (CS34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (X4 ∷ CCZ023 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wp0406 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff014 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wp0406 c4 = pw2 c4 (CS34 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wp0407 : Complete 4 → ⟪ (S4⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ023 ∷ X4 ∷ S4⁻ ∷ []) ⟫ʷ
wp0407 c4 = pw1 c4 (S4⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (X4 ∷ CCZ023 ∷ X4 ∷ S4⁻ ∷ []) tt tt Eq.refl

wp0408 : Complete 4 → ⟪ (S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff014 ∷ X4 ∷ S4⁻ ∷ []) ⟫ʷ
wp0408 c4 = pw2 c4 (S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ S4⁻ ∷ []) tt tt Eq.refl

wp0409 : Complete 4 → ⟪ (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ []) ⟫ʷ
wp0409 c4 = pw2 c4 (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ []) tt tt Eq.refl

wp0410 : Complete 4 → ⟪ (K2 ∷ CS24 ∷ K2 ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ []) ⟫ʷ
wp0410 c4 = pw1 c4 (K2 ∷ CS24 ∷ K2 ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) (X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ []) tt tt Eq.refl

wp0411 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS01 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wp0411 c4 = pw3 c4 (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (X4 ∷ CS01 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wp0412 : Complete 4 → ⟪ (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) ⟫ʷ
wp0412 c4 = pw1 c4 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) (X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) tt tt Eq.refl

wp0413 : Complete 4 → ⟪ (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ []) ⟫ʷ
wp0413 c4 = pw3 c4 (K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) (X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX14 ∷ K2⁻ ∷ K2 ∷ CS12 ∷ K2⁻ ∷ []) tt tt Eq.refl

wp0414 : Complete 4 → ⟪ (CX14 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff013 ∷ X4 ∷ CX14 ∷ []) ⟫ʷ
wp0414 c4 = pw2 c4 (CX14 ∷ X4 ∷ Toff013 ∷ X4 ∷ []) (X4 ∷ Toff013 ∷ X4 ∷ CX14 ∷ []) tt tt Eq.refl

wp0415 : Complete 4 → ⟪ (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS01 ∷ X4 ∷ CS24⁻ ∷ []) ⟫ʷ
wp0415 c4 = pw3 c4 (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (X4 ∷ CS01 ∷ X4 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wp0416 : Complete 4 → ⟪ (CS24⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS03⁻ ∷ X4 ∷ CS24⁻ ∷ []) ⟫ʷ
wp0416 c4 = pw1 c4 (CS24⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ X4 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wp0417 : Complete 4 → ⟪ (CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS03 ∷ X4 ∷ CS24⁻ ∷ []) ⟫ʷ
wp0417 c4 = pw1 c4 (CS24⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wp0418 : Complete 4 → ⟪ (CCZ012 ∷ Toff104 ∷ CS12 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ CS12 ∷ Toff104 ∷ CCZ012 ∷ []) ⟫ʷ
wp0418 c4 = pw3 c4 (CCZ012 ∷ Toff104 ∷ CS12 ∷ Toff104 ∷ []) (Toff104 ∷ CS12 ∷ Toff104 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0419 : Complete 4 → ⟪ (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) ⟫ʷ
wp0419 c4 = pw2 c4 (K1 ∷ CS14 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ K1⁻ ∷ []) tt tt Eq.refl

wp0420 : Complete 4 → ⟪ (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ023 ∷ X4 ∷ CX34 ∷ []) ⟫ʷ
wp0420 c4 = pw1 c4 (CX34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (X4 ∷ CCZ023 ∷ X4 ∷ CX34 ∷ []) tt tt Eq.refl

wp0421 : Complete 4 → ⟪ (CS14⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS03⁻ ∷ X4 ∷ CS14⁻ ∷ []) ⟫ʷ
wp0421 c4 = pw2 c4 (CS14⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ X4 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wp0422 : Complete 4 → ⟪ (CS14⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS03 ∷ X4 ∷ CS14⁻ ∷ []) ⟫ʷ
wp0422 c4 = pw2 c4 (CS14⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wp0423 : Complete 4 → ⟪ (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) ⟫ʷ
wp0423 c4 = pw2 c4 (K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS14⁻ ∷ K1⁻ ∷ K1 ∷ CX34 ∷ K1⁻ ∷ K1 ∷ CS13 ∷ K1⁻ ∷ []) tt tt Eq.refl

wp0424 : Complete 4 → ⟪ (S4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ013 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wp0424 c4 = pw2 c4 (S4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wp0425 : Complete 4 → ⟪ (S4 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff024 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wp0425 c4 = pw1 c4 (S4 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wp0426 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS12⁻ ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0426 c4 = pw3 c4 (CS04 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12⁻ ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0427 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff134 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0427 c4 = pw2 c4 (CS04 ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (X4 ∷ Toff134 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0428 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ013 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0428 c4 = pw2 c4 (CS04 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0429 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff024 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0429 c4 = pw1 c4 (CS04 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0430 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ013 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wp0430 c4 = pw2 c4 (CS14 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wp0431 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff024 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wp0431 c4 = pw3 c4 (CS14 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wp0432 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS01⁻ ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wp0432 c4 = pw3 c4 (CS24 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (X4 ∷ CS01⁻ ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wp0433 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff024 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wp0433 c4 = pw1 c4 (CS24 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wp0434 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ013 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wp0434 c4 = pw2 c4 (CS34 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wp0435 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff024 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wp0435 c4 = pw1 c4 (CS34 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wp0436 : Complete 4 → ⟪ (S4⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ013 ∷ X4 ∷ S4⁻ ∷ []) ⟫ʷ
wp0436 c4 = pw2 c4 (S4⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ X4 ∷ S4⁻ ∷ []) tt tt Eq.refl

wp0437 : Complete 4 → ⟪ (S4⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff024 ∷ X4 ∷ S4⁻ ∷ []) ⟫ʷ
wp0437 c4 = pw1 c4 (S4⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ S4⁻ ∷ []) tt tt Eq.refl

wp0438 : Complete 4 → ⟪ (K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ []) ⟫ʷ
wp0438 c4 = pw1 c4 (K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ []) tt tt Eq.refl

wp0439 : Complete 4 → ⟪ (K3 ∷ CS34 ∷ K3 ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ []) ⟫ʷ
wp0439 c4 = pw1 c4 (K3 ∷ CS34 ∷ K3 ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ []) tt tt Eq.refl

wp0440 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS02 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wp0440 c4 = pw1 c4 (CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (X4 ∷ CS02 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wp0441 : Complete 4 → ⟪ (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) ⟫ʷ
wp0441 c4 = pw1 c4 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) tt tt Eq.refl
