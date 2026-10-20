{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00127 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X15 ; _•_ ; _≈_ ; by-assoc-and ; p ; s3 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00092 as E

proved : p (s3) • X15 ≈ X15 • p (s3)
proved = by-assoc-and E.proved Eq.refl Eq.refl
