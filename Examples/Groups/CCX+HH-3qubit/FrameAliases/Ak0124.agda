{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameAliases.Ak0124 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0124 ; NK ; _•_ ; _≈_ ; by-assoc-and ; cong ; forget-frame ; k0124 ; p ; refl ; s3 ; trans ; module Eq)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B000 using (module PE00004 ; module PE00213)
import Examples.Groups.CCX+HH-3qubit.GatePermutations as GP

step0 : k0124 ≈ p (s3) • NK • p (s3)
step0 = by-assoc-and (cong (GP.gatet34) (cong (refl {w = NK}) (GP.gatet34))) Eq.refl Eq.refl

step1 : p (s3) • NK • p (s3) ≈ p (s3) • NK • p (s3)
step1 = cong refl (cong refl PE00004.proved)

step2 : p (s3) • NK • p (s3) ≈ K0124
step2 = forget-frame (by-assoc-and MV00245.proved Eq.refl Eq.refl) (by-assoc-and PE00213.proved Eq.refl Eq.refl)

proved : k0124 ≈ K0124
proved = trans step0 (trans step1 step2)
