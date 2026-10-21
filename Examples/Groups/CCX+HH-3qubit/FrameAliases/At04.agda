{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameAliases.At04 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X04 ; _•_ ; _≈_ ; by-assoc-and ; cong ; p ; s0 ; s1 ; s2 ; s3 ; t04 ; trans ; module Eq)
open K
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B001 using (module PE00955)
import Examples.Groups.CCX+HH-3qubit.GatePermutations as GP

step0 : t04 ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s0)
step0 = by-assoc-and (cong (GP.gatet01) (cong (GP.gatet12) (cong (GP.gatet23) (cong (GP.gatet34) (cong (GP.gatet23) (cong (GP.gatet12) (GP.gatet01))))))) Eq.refl Eq.refl

proved : t04 ≈ X04
proved = trans step0 (by-assoc-and PE00955.proved Eq.refl Eq.refl)
