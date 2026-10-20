{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameAliases.At13 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X13 ; _•_ ; _≈_ ; by-assoc-and ; cong ; p ; s1 ; s2 ; t13 ; trans ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00956 as E
import Examples.Groups.CCX+HH-3qubit.GatePermutations as GP

step0 : t13 ≈ p (s1 • s2 • s1)
step0 = by-assoc-and (cong (GP.gatet12) (cong (GP.gatet23) (GP.gatet12))) Eq.refl Eq.refl

proved : t13 ≈ X13
proved = trans step0 (by-assoc-and E.proved Eq.refl Eq.refl)
