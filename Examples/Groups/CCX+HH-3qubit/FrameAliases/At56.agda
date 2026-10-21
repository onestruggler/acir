{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameAliases.At56 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X56 ; _≈_ ; by-assoc-and ; p ; s5 ; t56 ; trans ; module Eq)
open K
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B001 using (module PE00006)
import Examples.Groups.CCX+HH-3qubit.GatePermutations as GP

step0 : t56 ≈ p (s5)
step0 = by-assoc-and (GP.gatet56) Eq.refl Eq.refl

proved : t56 ≈ X56
proved = trans step0 (by-assoc-and PE00006.proved Eq.refl Eq.refl)
