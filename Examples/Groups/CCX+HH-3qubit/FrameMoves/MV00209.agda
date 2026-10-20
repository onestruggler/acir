{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00209 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X35 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; p ; s3 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00174 as E

proved : p (s3) • X45 ≈ X35 • p (s3)
proved = by-assoc-and E.proved Eq.refl Eq.refl
