{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameAliases.Ak2345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2345 ; NK ; _•_ ; _≈_ ; by-assoc-and ; cong ; forget-frame ; k2345 ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; trans ; module Eq)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00634)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B000 using (module PE00953 ; module PE00954)
import Examples.Groups.CCX+HH-3qubit.GatePermutations as GP

step0 : k2345 ≈ p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)
step0 = by-assoc-and (cong (cong (cong (GP.gatet01) (cong (GP.gatet12) (GP.gatet01))) (cong (cong (GP.gatet12) (cong (GP.gatet23) (GP.gatet12))) (cong (cong (GP.gatet23) (cong (GP.gatet34) (GP.gatet23))) (cong (GP.gatet34) (cong (GP.gatet45) (GP.gatet34)))))) (cong (refl {w = NK}) (cong (cong (GP.gatet34) (cong (GP.gatet45) (GP.gatet34))) (cong (cong (GP.gatet23) (cong (GP.gatet34) (GP.gatet23))) (cong (cong (GP.gatet12) (cong (GP.gatet23) (GP.gatet12))) (cong (GP.gatet01) (cong (GP.gatet12) (GP.gatet01)))))))) Eq.refl Eq.refl

step1 : p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0) ≈ p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)
step1 = cong refl (cong refl PE00953.proved)

step2 : p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0) ≈ K2345
step2 = forget-frame (by-assoc-and MV00634.proved Eq.refl Eq.refl) (by-assoc-and PE00954.proved Eq.refl Eq.refl)

proved : k2345 ≈ K2345
proved = trans step0 (trans step1 step2)
