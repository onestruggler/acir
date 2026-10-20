{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameAliases.Ak0124 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0124 ; NK ; _•_ ; _≈_ ; by-assoc-and ; cong ; forget-frame ; k0124 ; p ; refl ; s3 ; trans ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00245 as Move
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00004 as R
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00213 as Inv
import Examples.Groups.CCX+HH-3qubit.GatePermutations as GP

step0 : k0124 ≈ p (s3) • NK • p (s3)
step0 = by-assoc-and (cong (GP.gatet34) (cong (refl {w = NK}) (GP.gatet34))) Eq.refl Eq.refl

step1 : p (s3) • NK • p (s3) ≈ p (s3) • NK • p (s3)
step1 = cong refl (cong refl R.proved)

step2 : p (s3) • NK • p (s3) ≈ K0124
step2 = forget-frame (by-assoc-and Move.proved Eq.refl Eq.refl) (by-assoc-and Inv.proved Eq.refl Eq.refl)

proved : k0124 ≈ K0124
proved = trans step0 (trans step1 step2)
