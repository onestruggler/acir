{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameAliases.At67 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X67 ; _≈_ ; by-assoc-and ; p ; s6 ; t67 ; trans ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00007 as E
import Examples.Groups.CCX+HH-3qubit.GatePermutations as GP

step0 : t67 ≈ p (s6)
step0 = by-assoc-and (GP.gatet67) Eq.refl Eq.refl

proved : t67 ≈ X67
proved = trans step0 (by-assoc-and E.proved Eq.refl Eq.refl)
