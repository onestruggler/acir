{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00161 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X25 ; _•_ ; _≈_ ; by-assoc-and ; p ; s3 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00126 as E

proved : p (s3) • X25 ≈ X25 • p (s3)
proved = by-assoc-and E.proved Eq.refl Eq.refl
